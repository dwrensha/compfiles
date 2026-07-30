/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Nat.Totient
public import Mathlib.GroupTheory.DedekindFinite
public import Mathlib.Order.Circular
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.LinearCombination.Lemmas
public import ProblemExtraction

@[expose] public section

-- This file's proofs are memory-bound: asynchronous elaboration retains per-tactic
-- snapshots whose peak exceeds 3 GiB. Elaborating synchronously keeps peak RSS near
-- 2.5 GiB at the cost of some wall-clock time.
set_option Elab.async false

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Olympiad 2013, Problem 6

Let n ≥ 3 be an integer, and consider a circle with n + 1 equally spaced points
marked on it. Consider all labellings of these points with the numbers 0, 1, ..., n
such that each label is used exactly once; two such labellings are considered to be
the same if one can be obtained from the other by a rotation of the circle. A
labelling is called beautiful if, for any four labels a < b < c < d with a + d = b + c,
the chord joining the points labelled a and d does not intersect the chord joining
the points labelled b and c. Let M be the number of beautiful labellings, and let N
be the number of ordered pairs (x, y) of positive integers such that x + y ≤ n and
gcd(x, y) = 1. Prove that M = N + 1.
-/

namespace Imo2013P6

open Finset

snip begin

/-!
## Circular order on `ZMod (n+1)`

We view the `n + 1` marked points on the circle as the type `ZMod (n + 1)`, with the
circular order obtained by "closing the necklace" of the linear order on `Fin (n + 1)`
(recall that `ZMod (n + 1)` is definitionally `Fin (n + 1)`). The strict betweenness
`sbtw a b c` means that `b` lies on the counterclockwise arc from `a` to `c`.
-/

instance instCircularOrderZModN (N : ℕ) [NeZero N] : CircularOrder (ZMod N) where
  btw a b c := (a.val ≤ b.val ∧ b.val ≤ c.val) ∨ (b.val ≤ c.val ∧ c.val ≤ a.val) ∨
    (c.val ≤ a.val ∧ a.val ≤ b.val)
  sbtw a b c := (a.val < b.val ∧ b.val < c.val) ∨ (b.val < c.val ∧ c.val < a.val) ∨
    (c.val < a.val ∧ a.val < b.val)
  btw_refl a := Or.inl ⟨le_rfl, le_rfl⟩
  btw_cyclic_left := by
    intro a b c
    show ((a.val ≤ b.val ∧ b.val ≤ c.val) ∨ (b.val ≤ c.val ∧ c.val ≤ a.val) ∨
        (c.val ≤ a.val ∧ a.val ≤ b.val)) →
      ((b.val ≤ c.val ∧ c.val ≤ a.val) ∨ (c.val ≤ a.val ∧ a.val ≤ b.val) ∨
        (a.val ≤ b.val ∧ b.val ≤ c.val))
    rintro (⟨h1, h2⟩ | ⟨h2, h3⟩ | ⟨h3, h1⟩)
    · exact Or.inr (Or.inr ⟨h1, h2⟩)
    · exact Or.inl ⟨h2, h3⟩
    · exact Or.inr (Or.inl ⟨h3, h1⟩)
  sbtw_trans_left := by
    intro a b c d
    show ((a.val < b.val ∧ b.val < c.val) ∨ (b.val < c.val ∧ c.val < a.val) ∨
        (c.val < a.val ∧ a.val < b.val)) →
      ((b.val < d.val ∧ d.val < c.val) ∨ (d.val < c.val ∧ c.val < b.val) ∨
        (c.val < b.val ∧ b.val < d.val)) →
      ((a.val < d.val ∧ d.val < c.val) ∨ (d.val < c.val ∧ c.val < a.val) ∨
        (c.val < a.val ∧ a.val < d.val))
    rintro (⟨h1, h2⟩ | ⟨h2, h3⟩ | ⟨h3, h1⟩) (⟨i1, i2⟩ | ⟨i2, i3⟩ | ⟨i3, i1⟩)
    · exact Or.inl ⟨by omega, i2⟩
    · exact Or.inl ⟨by omega, by omega⟩
    · exact Or.inl ⟨by omega, by omega⟩
    · exact Or.inr (Or.inl ⟨i2, h3⟩)
    · exact Or.inr (Or.inl ⟨by omega, by omega⟩)
    · exact Or.inr (Or.inl ⟨by omega, by omega⟩)
    · exact Or.inl ⟨by omega, i2⟩
    · exact Or.inr (Or.inl ⟨i2, h3⟩)
    · exact Or.inr (Or.inr ⟨h3, by omega⟩)
  sbtw_iff_btw_not_btw := by
    intro a b c
    show ((a.val < b.val ∧ b.val < c.val) ∨ (b.val < c.val ∧ c.val < a.val) ∨
        (c.val < a.val ∧ a.val < b.val)) ↔
      ((a.val ≤ b.val ∧ b.val ≤ c.val) ∨ (b.val ≤ c.val ∧ c.val ≤ a.val) ∨
        (c.val ≤ a.val ∧ a.val ≤ b.val)) ∧
        ¬((c.val ≤ b.val ∧ b.val ≤ a.val) ∨ (b.val ≤ a.val ∧ a.val ≤ c.val) ∨
          (a.val ≤ c.val ∧ c.val ≤ b.val))
    omega
  btw_antisymm := by
    intro a b c
    show ((a.val ≤ b.val ∧ b.val ≤ c.val) ∨ (b.val ≤ c.val ∧ c.val ≤ a.val) ∨
        (c.val ≤ a.val ∧ a.val ≤ b.val)) →
      ((c.val ≤ b.val ∧ b.val ≤ a.val) ∨ (b.val ≤ a.val ∧ a.val ≤ c.val) ∨
        (a.val ≤ c.val ∧ c.val ≤ b.val)) →
      (a = b ∨ b = c ∨ c = a)
    rintro (⟨h1, h2⟩ | ⟨h2, h3⟩ | ⟨h3, h1⟩) (⟨i1, i2⟩ | ⟨i2, i3⟩ | ⟨i3, i1⟩)
    · exact Or.inl (ZMod.val_injective _ (by omega : a.val = b.val))
    · exact Or.inl (ZMod.val_injective _ (by omega : a.val = b.val))
    · exact Or.inr (Or.inl (ZMod.val_injective _ (by omega : b.val = c.val)))
    · exact Or.inr (Or.inl (ZMod.val_injective _ (by omega : b.val = c.val)))
    · exact Or.inr (Or.inr (ZMod.val_injective _ (by omega : c.val = a.val)))
    · exact Or.inr (Or.inl (ZMod.val_injective _ (by omega : b.val = c.val)))
    · exact Or.inl (ZMod.val_injective _ (by omega : a.val = b.val))
    · exact Or.inl (ZMod.val_injective _ (by omega : a.val = b.val))
    · exact Or.inr (Or.inr (ZMod.val_injective _ (by omega : c.val = a.val)))
  btw_total := by
    intro a b c
    have ha := ZMod.val_lt a; have hb := ZMod.val_lt b; have hc := ZMod.val_lt c
    show ((a.val ≤ b.val ∧ b.val ≤ c.val) ∨ (b.val ≤ c.val ∧ c.val ≤ a.val) ∨
        (c.val ≤ a.val ∧ a.val ≤ b.val)) ∨
      ((c.val ≤ b.val ∧ b.val ≤ a.val) ∨ (b.val ≤ a.val ∧ a.val ≤ c.val) ∨
        (a.val ≤ c.val ∧ c.val ≤ b.val))
    omega

instance instCircularOrderZMod (n : ℕ) : CircularOrder (ZMod (n + 1)) :=
  instCircularOrderZModN (n + 1)

/-- Strict betweenness on `ZMod N` as a disjunction of value comparisons. -/
theorem sbtw_zmod_def {N : ℕ} [NeZero N] (a b c : ZMod N) :
    sbtw a b c ↔ (a.val < b.val ∧ b.val < c.val) ∨ (b.val < c.val ∧ c.val < a.val) ∨
      (c.val < a.val ∧ a.val < b.val) :=
  Iff.rfl

/-- Betweenness on `ZMod N` as a disjunction of value comparisons. -/
theorem btw_zmod_def {N : ℕ} [NeZero N] (a b c : ZMod N) :
    btw a b c ↔ (a.val ≤ b.val ∧ b.val ≤ c.val) ∨ (b.val ≤ c.val ∧ c.val ≤ a.val) ∨
      (c.val ≤ a.val ∧ a.val ≤ b.val) :=
  Iff.rfl

theorem val_sub' {N : ℕ} [NeZero N] (x a : ZMod N) :
    (x - a).val = (x.val + N - a.val) % N := by
  have h0 : ((N : ℕ) : ZMod N) = 0 := ZMod.natCast_self N
  have h1 : (x - a : ZMod N) = ((x.val + N - a.val : ℕ) : ZMod N) := by
    have ha : a.val ≤ x.val + N := by have := ZMod.val_lt a; omega
    rw [Nat.cast_sub ha, Nat.cast_add, h0, add_zero, ZMod.natCast_zmod_val,
      ZMod.natCast_zmod_val]
  rw [h1, ZMod.val_natCast]

/-- Strict betweenness via differences, the workhorse for computations. -/
theorem sbtw_val {N : ℕ} [NeZero N] {a b c : ZMod N} (hab : a ≠ b) :
    sbtw a b c ↔ (b - a).val < (c - a).val := by
  rw [sbtw_zmod_def, val_sub' b a, val_sub' c a]
  have ha := ZMod.val_lt a
  have hab' : a.val ≠ b.val := fun h => hab (ZMod.val_injective _ h)
  have key : ∀ x : ZMod N, (x.val + N - a.val) % N =
      if a.val ≤ x.val then x.val - a.val else x.val + N - a.val := by
    intro x
    have hxl := ZMod.val_lt x
    by_cases hx : a.val ≤ x.val
    · rw [if_pos hx]
      have e : x.val + N - a.val = (x.val - a.val) + N := by omega
      rw [e, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : x.val - a.val < N)]
    · rw [if_neg hx, Nat.mod_eq_of_lt (by omega : x.val + N - a.val < N)]
  rw [key b, key c]
  have hb := ZMod.val_lt b; have hc := ZMod.val_lt c
  by_cases h1 : a.val ≤ b.val <;> by_cases h2 : a.val ≤ c.val <;> simp [h1, h2] <;> omega

/-- If `a.val ≤ c.val`, strict betweenness from `a` to `c` is the plain value
interval: a single conjunction, avoiding the disjunction blowup in `omega`. -/
theorem sbtw_of_val_le {N : ℕ} [NeZero N] {a b c : ZMod N} (hac : a.val ≤ c.val) :
    sbtw a b c ↔ a.val < b.val ∧ b.val < c.val := by
  rw [sbtw_zmod_def]; omega

/-- If both `b.val` and `c.val` are at most `a.val`, strict betweenness from `a`
wraps around to below `c`: again a single conjunction. -/
theorem sbtw_of_val_ge {N : ℕ} [NeZero N] {a b c : ZMod N} (hb : b.val ≤ a.val)
    (hc : c.val ≤ a.val) : sbtw a b c ↔ b.val < c.val ∧ c.val < a.val := by
  rw [sbtw_zmod_def]; omega

/-- If `b.val` exceeds both `a.val` and `c.val`, `b` is the top point and strict
betweenness from `a` to `c` through `b` collapses to one comparison. -/
theorem sbtw_of_lt_max {N : ℕ} [NeZero N] {a b c : ZMod N} (ha : a.val < b.val)
    (hc : c.val < b.val) : sbtw a b c ↔ c.val < a.val := by
  rw [sbtw_zmod_def]; omega

/-- If `b.val` is below both `a.val` and `c.val`, `b` is the bottom point and strict
betweenness from `a` to `c` through `b` collapses to one comparison. -/
theorem sbtw_of_gt_min {N : ℕ} [NeZero N] {a b c : ZMod N} (ha : b.val < a.val)
    (hc : b.val < c.val) : sbtw a b c ↔ b.val < c.val ∧ c.val < a.val := by
  rw [sbtw_zmod_def]; omega

/-- Strict betweenness with left endpoint `0` is the plain value interval: a single
conjunction, much cheaper for `omega` than the three-way disjunction. -/
theorem sbtw_zero_left {N : ℕ} [NeZero N] (u v : ZMod N) :
    sbtw 0 u v ↔ 0 < u.val ∧ u.val < v.val := by
  rw [sbtw_zmod_def, ZMod.val_zero]; omega

/-- Strict betweenness with right endpoint `0` collapses to a single conjunction. -/
theorem sbtw_zero_right {N : ℕ} [NeZero N] (a u : ZMod N) :
    sbtw a u 0 ↔ 0 < a.val ∧ a.val < u.val := by
  rw [sbtw_zmod_def, ZMod.val_zero]; omega

/-- Strict betweenness with middle point `0` collapses to a single conjunction. -/
theorem sbtw_zero_mid {N : ℕ} [NeZero N] (a b : ZMod N) :
    sbtw a 0 b ↔ 0 < b.val ∧ b.val < a.val := by
  rw [sbtw_zmod_def, ZMod.val_zero]; omega

/-- If `c.val < a.val`, strict betweenness from `a` wraps around, giving a two-way
disjunction (cheaper for `omega` than the three-way one). -/
theorem sbtw_of_val_gt {N : ℕ} [NeZero N] {a b c : ZMod N} (hac : c.val < a.val) :
    sbtw a b c ↔ b.val < c.val ∨ a.val < b.val := by
  rw [sbtw_zmod_def]; omega

/-- Translation by `t` preserves strict betweenness. -/
theorem sbtw_add {N : ℕ} [NeZero N] {a b c : ZMod N} (t : ZMod N) (hab : a ≠ b) :
    sbtw (a + t) (b + t) (c + t) ↔ sbtw a b c := by
  have hab' : a + t ≠ b + t := fun h => hab (add_left_injective t h)
  have e1 : b + t - (a + t) = b - a := by ring
  have e2 : c + t - (a + t) = c - a := by ring
  rw [sbtw_val hab', sbtw_val hab, e1, e2]

instance decidableSbtwZMod {N : ℕ} [NeZero N] (a b c : ZMod N) : Decidable (sbtw a b c) :=
  decidable_of_iff _ (sbtw_zmod_def a b c).symm

instance decidableBtwZMod {N : ℕ} [NeZero N] (a b c : ZMod N) : Decidable (btw a b c) :=
  decidable_of_iff _ (btw_zmod_def a b c).symm

/-! ## Beautiful labellings -/

/-- The chords joining `p` to `q` and `r` to `s` cross, i.e. `r` and `s` lie on
different open arcs determined by `p` and `q`. (Used only when `p, q, r, s` are
pairwise distinct.) -/
def Crossing {N : ℕ} [NeZero N] (p q r s : ZMod N) : Prop :=
  sbtw p r q ≠ sbtw p s q

/-- A labelling `σ` (a bijection between labels and positions, both indexed by
`ZMod N`) is beautiful if for any four labels `a < b < c < d` with
`a + d = b + c`, the chord joining the points labelled `a` and `d` does not cross
the chord joining the points labelled `b` and `c`. -/
def Beautiful {N : ℕ} [NeZero N] (σ : ZMod N ≃ ZMod N) : Prop :=
  ∀ a b c d : ZMod N, a.val < b.val → b.val < c.val → c.val < d.val →
    a.val + d.val = b.val + c.val → ¬ Crossing (σ a) (σ d) (σ b) (σ c)

instance {N : ℕ} [NeZero N] (σ : ZMod N ≃ ZMod N) : Decidable (Beautiful σ) := by
  unfold Beautiful Crossing
  infer_instance

/-- Rotation of a labelling: all positions shifted by `t`. -/
def rot {N : ℕ} [NeZero N] (t : ZMod N) (σ : ZMod N ≃ ZMod N) :
    ZMod N ≃ ZMod N :=
  σ.trans (Equiv.addRight t)

theorem rot_apply {N : ℕ} [NeZero N] (t : ZMod N) (σ : ZMod N ≃ ZMod N)
    (x : ZMod N) : rot t σ x = σ x + t := rfl

@[simp]
theorem rot_zero {N : ℕ} [NeZero N] (σ : ZMod N ≃ ZMod N) : rot 0 σ = σ := by
  ext x
  simp [rot_apply]

theorem rot_rot {N : ℕ} [NeZero N] (s t : ZMod N) (σ : ZMod N ≃ ZMod N) :
    rot s (rot t σ) = rot (s + t) σ := by
  ext x
  rw [rot_apply, rot_apply, rot_apply, add_assoc, add_comm t s]

/-- Beauty is invariant under rotation. -/
theorem Beautiful.rot {N : ℕ} [NeZero N] {σ : ZMod N ≃ ZMod N} (h : Beautiful σ)
    (t : ZMod N) : Beautiful (rot t σ) := by
  intro a b c d hab hbc hcd hsum hc
  apply h a b c d hab hbc hcd hsum
  have key : ∀ x y : ZMod N, x.val < y.val → σ x ≠ σ y := by
    intro x y hxy he
    rw [σ.injective he] at hxy
    exact absurd hxy (lt_irrefl _)
  simp only [rot_apply] at hc
  unfold Crossing at hc ⊢
  rwa [sbtw_add t (key a b hab), sbtw_add t (key a c (hab.trans hbc))] at hc

theorem val_sub_if {N : ℕ} [NeZero N] (x y : ZMod N) :
    (y - x).val = if x.val ≤ y.val then y.val - x.val else y.val + N - x.val := by
  rw [val_sub' y x]
  by_cases h : x.val ≤ y.val
  · rw [if_pos h]
    have e : y.val + N - x.val = (y.val - x.val) + N := by omega
    rw [e, Nat.add_mod_right, Nat.mod_eq_of_lt]
    have := ZMod.val_lt y
    omega
  · rw [if_neg h, Nat.mod_eq_of_lt]
    have := ZMod.val_lt y
    have := ZMod.val_lt x
    omega

/-- Insertion of a new point at position `q` of the circle `ZMod (n + 2)`: the map from
the old circle `ZMod (n + 1)` to the new one, placing the old point `x` at position
`q + 1 + x.val`. Its image is exactly the complement of `q`. -/
def circleIncl {n : ℕ} (q : ZMod (n + 2)) (x : ZMod (n + 1)) : ZMod (n + 2) :=
  q + 1 + x.val

theorem circleIncl_ne_q {n : ℕ} (q : ZMod (n + 2)) (x : ZMod (n + 1)) :
    circleIncl q x ≠ q := by
  intro h
  unfold circleIncl at h
  have h1 : (1 : ZMod (n + 2)) + x.val = 0 := by
    have h2 : q + ((1 : ZMod (n + 2)) + x.val) = q + 0 := by
      rw [show q + ((1 : ZMod (n + 2)) + x.val) = q + 1 + x.val from by ring, h, add_zero]
    exact add_left_cancel h2
  have h2 : (x.val : ZMod (n + 2)) = -1 := by linear_combination h1
  have h3 : (x.val : ZMod (n + 2)).val = x.val :=
    ZMod.val_cast_of_lt (by have := ZMod.val_lt x; omega)
  have h4 : ((-1 : ZMod (n + 2))).val = n + 1 := by
    have h5 : ((-1 : ZMod (n + 2))) = ((n + 1 : ℕ) : ZMod (n + 2)) := by
      rw [neg_eq_iff_add_eq_zero, ← Nat.cast_one, ← Nat.cast_add]
      have : 1 + (n + 1) = n + 2 := by omega
      rw [this, ZMod.natCast_self]
    rw [h5, ZMod.val_cast_of_lt (by omega : n + 1 < n + 2)]
  rw [h2, h4] at h3
  have := ZMod.val_lt x
  omega

theorem circleIncl_injective {n : ℕ} (q : ZMod (n + 2)) :
    Function.Injective (circleIncl q) := by
  intro x y h
  unfold circleIncl at h
  have h1 : (x.val : ZMod (n + 2)) = y.val := by
    have := add_left_cancel_iff (a := q + 1) (b := (x.val : ZMod (n + 2)))
      (c := (y.val : ZMod (n + 2)))
    exact add_left_cancel_iff.mp h
  have h2 : (x.val : ZMod (n + 2)).val = x.val :=
    ZMod.val_cast_of_lt (by have := ZMod.val_lt x; omega)
  have h3 : (y.val : ZMod (n + 2)).val = y.val :=
    ZMod.val_cast_of_lt (by have := ZMod.val_lt y; omega)
  have h4 : x.val = y.val := by rw [← h2, h1, h3]
  exact ZMod.val_injective _ h4

/-- The strict betweenness preservation of `circleIncl`: the main computation. -/
theorem circleIncl_sbtw {n : ℕ} {q : ZMod (n + 2)} {x y z : ZMod (n + 1)} (hxy : x ≠ y) :
    sbtw (circleIncl q x) (circleIncl q y) (circleIncl q z) ↔ sbtw x y z := by
  have hxy' : circleIncl q x ≠ circleIncl q y :=
    fun h => hxy (circleIncl_injective q h)
  have hxv : ((x.val : ZMod (n + 2))).val = x.val :=
    ZMod.val_cast_of_lt (by have := ZMod.val_lt x; omega)
  have hyv : ((y.val : ZMod (n + 2))).val = y.val :=
    ZMod.val_cast_of_lt (by have := ZMod.val_lt y; omega)
  have zv : ((z.val : ZMod (n + 2))).val = z.val :=
    ZMod.val_cast_of_lt (by have := ZMod.val_lt z; omega)
  have e2 : circleIncl q y - circleIncl q x = (y.val : ZMod (n + 2)) - x.val := by
    unfold circleIncl
    ring
  have e3 : circleIncl q z - circleIncl q x = (z.val : ZMod (n + 2)) - x.val := by
    unfold circleIncl
    ring
  have hxyv : (x.val : ZMod (n + 2)) ≠ (y.val : ZMod (n + 2)) := by
    intro h
    apply hxy
    apply ZMod.val_injective (n + 1)
    rw [← hxv, ← hyv, h]
  rw [sbtw_val hxy', e2, e3, val_sub' (y.val : ZMod (n + 2)) (x.val : ZMod (n + 2)),
    val_sub' (z.val : ZMod (n + 2)) (x.val : ZMod (n + 2)), hxv, hyv, zv]
  rw [sbtw_val hxy, val_sub' y x, val_sub' z x]
  have hx := ZMod.val_lt x; have hy := ZMod.val_lt y; have hz := ZMod.val_lt z
  by_cases h1 : x.val ≤ y.val
  · have m1 : (y.val + (n + 2) - x.val) % (n + 2) = y.val - x.val := by
      have e' : y.val + (n + 2) - x.val = (y.val - x.val) + (n + 2) := by omega
      rw [e', Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : y.val - x.val < n + 2)]
    have m1' : (y.val + (n + 1) - x.val) % (n + 1) = y.val - x.val := by
      have e' : y.val + (n + 1) - x.val = (y.val - x.val) + (n + 1) := by omega
      rw [e', Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : y.val - x.val < n + 1)]
    rw [m1, m1']
    by_cases h2 : x.val ≤ z.val
    · have m2 : (z.val + (n + 2) - x.val) % (n + 2) = z.val - x.val := by
        have e' : z.val + (n + 2) - x.val = (z.val - x.val) + (n + 2) := by omega
        rw [e', Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : z.val - x.val < n + 2)]
      have m2' : (z.val + (n + 1) - x.val) % (n + 1) = z.val - x.val := by
        have e' : z.val + (n + 1) - x.val = (z.val - x.val) + (n + 1) := by omega
        rw [e', Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : z.val - x.val < n + 1)]
      rw [m2, m2']
    · have m2 : (z.val + (n + 2) - x.val) % (n + 2) = z.val + (n + 2) - x.val :=
        Nat.mod_eq_of_lt (by omega : z.val + (n + 2) - x.val < n + 2)
      have m2' : (z.val + (n + 1) - x.val) % (n + 1) = z.val + (n + 1) - x.val :=
        Nat.mod_eq_of_lt (by omega : z.val + (n + 1) - x.val < n + 1)
      rw [m2, m2']
      omega
  · have m1 : (y.val + (n + 2) - x.val) % (n + 2) = y.val + (n + 2) - x.val :=
      Nat.mod_eq_of_lt (by omega : y.val + (n + 2) - x.val < n + 2)
    have m1' : (y.val + (n + 1) - x.val) % (n + 1) = y.val + (n + 1) - x.val :=
      Nat.mod_eq_of_lt (by omega : y.val + (n + 1) - x.val < n + 1)
    rw [m1, m1']
    by_cases h2 : x.val ≤ z.val
    · have m2 : (z.val + (n + 2) - x.val) % (n + 2) = z.val - x.val := by
        have e' : z.val + (n + 2) - x.val = (z.val - x.val) + (n + 2) := by omega
        rw [e', Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : z.val - x.val < n + 2)]
      have m2' : (z.val + (n + 1) - x.val) % (n + 1) = z.val - x.val := by
        have e' : z.val + (n + 1) - x.val = (z.val - x.val) + (n + 1) := by omega
        rw [e', Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : z.val - x.val < n + 1)]
      rw [m2, m2']
      omega
    · have m2 : (z.val + (n + 2) - x.val) % (n + 2) = z.val + (n + 2) - x.val :=
        Nat.mod_eq_of_lt (by omega : z.val + (n + 2) - x.val < n + 2)
      have m2' : (z.val + (n + 1) - x.val) % (n + 1) = z.val + (n + 1) - x.val :=
        Nat.mod_eq_of_lt (by omega : z.val + (n + 1) - x.val < n + 1)
      rw [m2, m2']
      omega

/-- The circle `ZMod (n + 1)` identified with the circle `ZMod (n + 2)` punctured at
`q`, preserving the circular order. -/
def circleIso {n : ℕ} (q : ZMod (n + 2)) : ZMod (n + 1) ≃ {z : ZMod (n + 2) // z ≠ q} where
  toFun x := ⟨circleIncl q x, circleIncl_ne_q q x⟩
  invFun y := ⟨(y.1 - q - 1).val, by
    have hne : (y.1 - q - 1).val ≠ n + 1 := by
      intro he
      apply y.2
      have h1 : (y.1 - q - 1 : ZMod (n + 2)) = -1 := by
        apply ZMod.val_injective (n + 2)
        rw [he]
        have h4 : ((-1 : ZMod (n + 2))).val = n + 1 := by
          have h5 : ((-1 : ZMod (n + 2))) = ((n + 1 : ℕ) : ZMod (n + 2)) := by
            rw [neg_eq_iff_add_eq_zero, ← Nat.cast_one, ← Nat.cast_add]
            have : 1 + (n + 1) = n + 2 := by omega
            rw [this, ZMod.natCast_self]
          rw [h5, ZMod.val_cast_of_lt (by omega : n + 1 < n + 2)]
        rw [h4]
      have h2 : y.1 = q := by linear_combination h1
      exact h2
    have := ZMod.val_lt (y.1 - q - 1)
    omega⟩
  left_inv x := by
    apply ZMod.val_injective (n + 1)
    show ((q + 1 + (x.val : ZMod (n + 2))) - q - 1).val = x.val
    have e : (q + 1 + (x.val : ZMod (n + 2))) - q - 1 = (x.val : ZMod (n + 2)) := by ring
    rw [e, ZMod.val_cast_of_lt (by have := ZMod.val_lt x; omega : x.val < n + 2)]
  right_inv y := by
    apply Subtype.ext
    show q + 1 + (((y.1 - q - 1).val : ℕ) : ZMod (n + 2)) = y.1
    rw [ZMod.natCast_zmod_val]
    ring

/-- The map from the punctured circle back to `ZMod (n + 1)`. -/
def cutCircle {n : ℕ} (q : ZMod (n + 2)) (y : {z : ZMod (n + 2) // z ≠ q}) : ZMod (n + 1) :=
  (circleIso q).symm y

theorem circleIncl_cutCircle {n : ℕ} (q : ZMod (n + 2)) (y : {z : ZMod (n + 2) // z ≠ q}) :
    circleIncl q (cutCircle q y) = y.1 := by
  have h := (circleIso q).right_inv y
  exact Subtype.ext_iff.mp h

/-- Strict betweenness preservation of `cutCircle`. -/
theorem cutCircle_sbtw {n : ℕ} {q : ZMod (n + 2)} (a b c : {z : ZMod (n + 2) // z ≠ q})
    (hab : a.1 ≠ b.1) :
    sbtw (cutCircle q a) (cutCircle q b) (cutCircle q c) ↔ sbtw a.1 b.1 c.1 := by
  have hab' : cutCircle q a ≠ cutCircle q b := by
    intro h
    apply hab
    rw [← circleIncl_cutCircle q a, ← circleIncl_cutCircle q b, h]
  rw [← circleIncl_sbtw (q := q) (x := cutCircle q a) (y := cutCircle q b)
    (z := cutCircle q c) hab']
  rw [circleIncl_cutCircle, circleIncl_cutCircle, circleIncl_cutCircle]

/-- Inclusion of labels `[0, n]` into `[0, n + 1]`. -/
def labelIncl {n : ℕ} (x : ZMod (n + 1)) : ZMod (n + 2) :=
  ((x.val : ℕ) : ZMod (n + 2))

theorem labelIncl_val {n : ℕ} (x : ZMod (n + 1)) : (labelIncl x).val = x.val :=
  ZMod.val_cast_of_lt (by have := ZMod.val_lt x; omega)

/-- The largest label `n + 1` as an element of `ZMod (n + 2)`. -/
def topLabel {n : ℕ} : ZMod (n + 2) :=
  ((n + 1 : ℕ) : ZMod (n + 2))

theorem topLabel_val {n : ℕ} : (topLabel : ZMod (n + 2)).val = n + 1 :=
  ZMod.val_cast_of_lt (by omega : n + 1 < n + 2)

theorem labelIncl_ne_top {n : ℕ} (x : ZMod (n + 1)) : labelIncl x ≠ topLabel := by
  intro h
  have h1 : (labelIncl x : ZMod (n + 2)).val = (topLabel : ZMod (n + 2)).val := by rw [h]
  rw [labelIncl_val, topLabel_val] at h1
  have := ZMod.val_lt x
  omega

theorem val_lt_of_ne_top {n : ℕ} {x : ZMod (n + 2)} (h : x ≠ topLabel) : x.val < n + 1 := by
  have h1 : x.val ≠ n + 1 := by
    intro he
    apply h
    rw [← ZMod.natCast_zmod_val x, he]
    rfl
  have := ZMod.val_lt x
  omega

theorem labelIncl_zero {n : ℕ} : labelIncl (0 : ZMod (n + 1)) = 0 := by
  unfold labelIncl
  rw [ZMod.val_zero, Nat.cast_zero]

/-- The equivalence between labels `[0, n]` and non-top labels of `[0, n + 1]`. -/
def labelInclEquiv {n : ℕ} : ZMod (n + 1) ≃ {z : ZMod (n + 2) // z ≠ topLabel} where
  toFun x := ⟨labelIncl x, labelIncl_ne_top x⟩
  invFun y := ((y.1.val : ℕ) : ZMod (n + 1))
  left_inv x := by
    show (((⟨labelIncl x, labelIncl_ne_top x⟩ : {z : ZMod (n + 2) // z ≠ topLabel}).1.val : ℕ) :
        ZMod (n + 1)) = x
    rw [labelIncl_val, ZMod.natCast_zmod_val]
  right_inv y := by
    apply Subtype.ext
    show labelIncl ((y.1.val : ℕ) : ZMod (n + 1)) = y.1
    unfold labelIncl
    have hy : y.1.val < n + 1 := val_lt_of_ne_top y.2
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hy, ZMod.natCast_zmod_val]

/-- Deletion of the largest label from a labelling of `[0, n + 1]`, producing a
labelling of `[0, n]`: positions are re-indexed by cutting the circle at the deleted
point. -/
def Del {n : ℕ} (S : ZMod (n + 2) ≃ ZMod (n + 2)) : ZMod (n + 1) ≃ ZMod (n + 1) :=
  labelInclEquiv.trans
    ((Equiv.subtypeEquiv S fun _ => not_congr (Equiv.apply_eq_iff_eq S).symm).trans
      (circleIso (S topLabel)).symm)

theorem Del_apply {n : ℕ} (S : ZMod (n + 2) ≃ ZMod (n + 2)) (x : ZMod (n + 1)) :
    Del S x = cutCircle (S topLabel) ⟨S (labelIncl x), by
      rw [S.injective.ne_iff]
      exact labelIncl_ne_top x⟩ :=
  rfl

/-- Deletion preserves beauty. -/
theorem Del_beautiful {n : ℕ} {S : ZMod (n + 2) ≃ ZMod (n + 2)} (h : Beautiful S) :
    Beautiful (Del S) := by
  intro a b c d hab hbc hcd hsum hcDel
  have hv : ∀ x : ZMod (n + 1), (labelIncl x : ZMod (n + 2)).val = x.val := labelIncl_val
  apply h (labelIncl a) (labelIncl b) (labelIncl c) (labelIncl d)
    (by rw [hv, hv]; exact hab) (by rw [hv, hv]; exact hbc) (by rw [hv, hv]; exact hcd)
    (by rw [hv, hv, hv, hv]; exact hsum)
  rw [Del_apply, Del_apply, Del_apply, Del_apply] at hcDel
  unfold Crossing at hcDel ⊢
  have inj : ∀ x y : ZMod (n + 1), x.val < y.val → S (labelIncl x) ≠ S (labelIncl y) := by
    intro x y hxy he
    have h1 : labelIncl x = labelIncl y := S.injective he
    have h2 : x.val = y.val := by rw [← labelIncl_val x, h1, labelIncl_val]
    omega
  rw [cutCircle_sbtw _ _ _ (inj a b hab), cutCircle_sbtw _ _ _ (inj a c (hab.trans hbc))]
    at hcDel
  exact hcDel

/-- The unique equivalence between two "singleton" subtypes. -/
def singletonEquiv {α : Type*} {a b : α} : {x : α // x = a} ≃ {y : α // y = b} where
  toFun _ := ⟨b, rfl⟩
  invFun _ := ⟨a, rfl⟩
  left_inv x := Subtype.ext x.2.symm
  right_inv y := Subtype.ext y.2.symm

/-- Insertion of the label `n + 1` at position `q` into a labelling of `[0, n]`,
producing a labelling of `[0, n + 1]`: the old label `x` is placed at position
`q + 1 + (τ x).val`. -/
def Insert {n : ℕ} (τ : ZMod (n + 1) ≃ ZMod (n + 1)) (q : ZMod (n + 2)) :
    ZMod (n + 2) ≃ ZMod (n + 2) :=
  Equiv.subtypeCongr (singletonEquiv (a := topLabel) (b := q))
    (labelInclEquiv.symm.trans (τ.trans (circleIso q)))

theorem Insert_top {n : ℕ} (τ : ZMod (n + 1) ≃ ZMod (n + 1)) (q : ZMod (n + 2)) :
    Insert τ q topLabel = q := by
  unfold Insert Equiv.subtypeCongr
  rw [Equiv.trans_apply, Equiv.trans_apply,
    Equiv.sumCompl_symm_apply_of_pos (p := fun x => x = topLabel) rfl]
  rfl

theorem Insert_apply_ne_top {n : ℕ} (τ : ZMod (n + 1) ≃ ZMod (n + 1)) (q : ZMod (n + 2))
    {x : ZMod (n + 2)} (hx : x ≠ topLabel) :
    Insert τ q x = circleIncl q (τ ((labelInclEquiv).symm ⟨x, hx⟩)) := by
  unfold Insert Equiv.subtypeCongr
  rw [Equiv.trans_apply, Equiv.trans_apply,
    Equiv.sumCompl_symm_apply_of_neg (p := fun x => x = topLabel) hx]
  rfl

theorem Del_apply_val {n : ℕ} (S : ZMod (n + 2) ≃ ZMod (n + 2)) (x : ZMod (n + 1)) :
    ((Del S) x).val = (S (labelIncl x) - S topLabel - 1).val := by
  rw [Del_apply]
  rfl

/-- Deletion undoes insertion. -/
theorem Del_Insert {n : ℕ} (τ : ZMod (n + 1) ≃ ZMod (n + 1)) (q : ZMod (n + 2)) :
    Del (Insert τ q) = τ := by
  ext x
  apply ZMod.val_injective (n + 1)
  rw [Del_apply_val]
  have ht : (Insert τ q) topLabel = q := Insert_top τ q
  have hx : labelIncl x ≠ topLabel := labelIncl_ne_top x
  rw [Insert_apply_ne_top (x := labelIncl x) (hx := hx)]
  rw [ht]
  have e1 : (labelInclEquiv).symm ⟨labelIncl x, hx⟩ = x := (labelInclEquiv).left_inv x
  rw [e1]
  have e2 : circleIncl q (τ x) - q - 1 = (τ x).val := by unfold circleIncl; ring
  rw [e2, ZMod.val_cast_of_lt (by have := ZMod.val_lt (τ x); omega : (τ x).val < n + 2)]

/-- Insertion undoes deletion. -/
theorem Insert_Del {n : ℕ} (S : ZMod (n + 2) ≃ ZMod (n + 2)) :
    Insert (Del S) (S topLabel) = S := by
  ext x
  by_cases hx : x = topLabel
  · rw [hx, Insert_top]
  · rw [Insert_apply_ne_top (Del S) (S topLabel) hx]
    have e1 : (labelInclEquiv).symm ⟨x, hx⟩ = ((x.val : ℕ) : ZMod (n + 1)) := rfl
    rw [e1, Del_apply]
    have e2 : labelIncl (((x.val : ℕ) : ZMod (n + 1))) = x := by
      unfold labelIncl
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt (val_lt_of_ne_top hx), ZMod.natCast_zmod_val]
    set y : {z : ZMod (n + 2) // z ≠ S topLabel} :=
      ⟨S (labelIncl ((x.val : ℕ) : ZMod (n + 1))), by
        rw [S.injective.ne_iff]
        exact labelIncl_ne_top _⟩ with hy
    rw [circleIncl_cutCircle]
    rw [hy]
    show S (labelIncl ((x.val : ℕ) : ZMod (n + 1))) = S x
    rw [e2]

/-- Normalized deletion: delete the largest label and rotate so that label `0` is back
at position `0`. -/
def DelNorm {n : ℕ} (S : ZMod (n + 2) ≃ ZMod (n + 2)) : ZMod (n + 1) ≃ ZMod (n + 1) :=
  rot (-((Del S) 0)) (Del S)

theorem DelNorm_zero {n : ℕ} (S : ZMod (n + 2) ≃ ZMod (n + 2)) : (DelNorm S) 0 = 0 := by
  unfold DelNorm
  rw [rot_apply, add_neg_cancel]

theorem DelNorm_beautiful {n : ℕ} {S : ZMod (n + 2) ≃ ZMod (n + 2)} (h : Beautiful S) :
    Beautiful (DelNorm S) :=
  Beautiful.rot (Del_beautiful h) _

/-- Normalized insertion: rotate `τ` by `c`, then insert the new largest label at the
unique position that places label `0` at position `0`. -/
def InsertNorm {n : ℕ} (τ : ZMod (n + 1) ≃ ZMod (n + 1)) (c : ZMod (n + 1)) :
    ZMod (n + 2) ≃ ZMod (n + 2) :=
  Insert (rot c τ) (((n + 1) - ((rot c τ) 0).val : ℕ) : ZMod (n + 2))

theorem InsertNorm_zero {n : ℕ} (τ : ZMod (n + 1) ≃ ZMod (n + 1)) (c : ZMod (n + 1)) :
    (InsertNorm τ c) 0 = 0 := by
  have h0 : (0 : ZMod (n + 2)) ≠ topLabel := by
    intro h
    have h1 : (0 : ZMod (n + 2)).val = (topLabel : ZMod (n + 2)).val := by rw [h]
    rw [topLabel_val, ZMod.val_zero] at h1
    omega
  unfold InsertNorm
  rw [Insert_apply_ne_top (x := 0) (hx := h0)]
  have e1 : (labelInclEquiv).symm ⟨(0 : ZMod (n + 2)), h0⟩ = 0 := by
    show (((0 : ZMod (n + 2)).val : ℕ) : ZMod (n + 1)) = 0
    rw [ZMod.val_zero, Nat.cast_zero]
  rw [e1]
  unfold circleIncl
  have e : ((n + 1) - ((rot c τ) 0).val + 1 + ((rot c τ) 0).val : ℕ) = n + 2 := by
    have := ZMod.val_lt ((rot c τ) 0)
    omega
  rw [show (((n + 1) - ((rot c τ) 0).val : ℕ) : ZMod (n + 2)) + 1 + (((rot c τ) 0).val : ZMod (n + 2))
      = ((((n + 1) - ((rot c τ) 0).val + 1 + ((rot c τ) 0).val) : ℕ) : ZMod (n + 2)) from by
    push_cast; ring]
  rw [e, ZMod.natCast_self]

theorem val_neg' {n : ℕ} {X : ZMod (n + 2)} (hX : X ≠ 0) : (-X).val = (n + 2) - X.val := by
  have h1 : X.val ≠ 0 := by
    intro he
    apply hX
    rw [← ZMod.natCast_zmod_val X, he]
    rfl
  have h2 : (-X : ZMod (n + 2)) = (((n + 2) - X.val : ℕ) : ZMod (n + 2)) := by
    rw [neg_eq_iff_add_eq_zero]
    conv_lhs => congr; rw [← ZMod.natCast_zmod_val X]
    rw [← Nat.cast_add, show X.val + ((n + 2) - X.val) = n + 2 from by
      have := ZMod.val_lt X; omega, ZMod.natCast_self]
  rw [h2, ZMod.val_natCast, Nat.mod_eq_of_lt (by have := ZMod.val_lt X; omega :
    (n + 2) - X.val < n + 2)]

theorem InsertNorm_DelNorm {n : ℕ} (S : ZMod (n + 2) ≃ ZMod (n + 2)) (hS : S 0 = 0) :
    InsertNorm (DelNorm S) ((Del S) 0) = S := by
  have h1 : rot ((Del S) 0) (DelNorm S) = Del S := by
    unfold DelNorm
    rw [rot_rot, add_neg_cancel, rot_zero]
  unfold InsertNorm
  rw [h1]
  have hq : (((n + 1) - ((Del S) 0).val : ℕ) : ZMod (n + 2)) = S topLabel := by
    suffices h : (n + 1) - ((Del S) 0).val = (S topLabel).val by
      rw [h, ZMod.natCast_zmod_val]
    rw [Del_apply_val, labelIncl_zero, hS]
    have e : (0 : ZMod (n + 2)) - S topLabel - 1 = -(S topLabel + 1) := by ring
    rw [e]
    by_cases hv : (S topLabel).val = n + 1
    · have htop : S topLabel = -1 := by
        rw [← ZMod.natCast_zmod_val (S topLabel), hv]
        have h5 : ((-1 : ZMod (n + 2))) = ((n + 1 : ℕ) : ZMod (n + 2)) := by
          rw [neg_eq_iff_add_eq_zero, ← Nat.cast_one, ← Nat.cast_add]
          have : 1 + (n + 1) = n + 2 := by omega
          rw [this, ZMod.natCast_self]
        rw [h5]
      rw [htop]
      simp
    · have hne : S topLabel + 1 ≠ 0 := by
        intro he
        apply hv
        have h5 : S topLabel = -1 := by linear_combination he
        have h6 : ((-1 : ZMod (n + 2))).val = n + 1 := by
          have h7 : ((-1 : ZMod (n + 2))) = ((n + 1 : ℕ) : ZMod (n + 2)) := by
            rw [neg_eq_iff_add_eq_zero, ← Nat.cast_one, ← Nat.cast_add]
            have : 1 + (n + 1) = n + 2 := by omega
            rw [this, ZMod.natCast_self]
          rw [h7, ZMod.val_cast_of_lt (by omega : n + 1 < n + 2)]
        rw [h5, h6]
      have hval : (S topLabel + 1).val = (S topLabel).val + 1 := by
        have e2 : (S topLabel + 1 : ZMod (n + 2)) = (((S topLabel).val + 1 : ℕ) : ZMod (n + 2)) := by
          conv_lhs => rw [← ZMod.natCast_zmod_val (S topLabel)]
          rw [← Nat.cast_one, ← Nat.cast_add]
        rw [e2, ZMod.val_natCast, Nat.mod_eq_of_lt (by have := ZMod.val_lt (S topLabel); omega :
          (S topLabel).val + 1 < n + 2)]
      rw [val_neg' hne, hval]
      have := ZMod.val_lt (S topLabel)
      omega
  rw [hq, Insert_Del]

theorem Del_InsertNorm {n : ℕ} (τ : ZMod (n + 1) ≃ ZMod (n + 1)) (c : ZMod (n + 1)) :
    Del (InsertNorm τ c) = rot c τ := by
  unfold InsertNorm
  rw [Del_Insert]

theorem Del_InsertNorm_zero {n : ℕ} (τ : ZMod (n + 1) ≃ ZMod (n + 1)) (c : ZMod (n + 1))
    (hτ : τ 0 = 0) : (Del (InsertNorm τ c)) 0 = c := by
  rw [Del_InsertNorm, rot_apply, hτ, zero_add]

theorem DelNorm_InsertNorm {n : ℕ} (τ : ZMod (n + 1) ≃ ZMod (n + 1)) (c : ZMod (n + 1))
    (hτ : τ 0 = 0) : DelNorm (InsertNorm τ c) = τ := by
  unfold DelNorm
  rw [Del_InsertNorm_zero τ c hτ, Del_InsertNorm, rot_rot, neg_add_cancel, rot_zero]

/-- A labelling of `[0, n]` is linear if it is an arithmetic progression modulo
`n + 1`, i.e. positions are given by multiplication by a unit. -/
def Linear {n : ℕ} (τ : ZMod (n + 1) ≃ ZMod (n + 1)) : Prop :=
  ∃ s : (ZMod (n + 1))ˣ, ∀ x, τ x = s * x

noncomputable instance {n : ℕ} (τ : ZMod (n + 1) ≃ ZMod (n + 1)) : Decidable (Linear τ) :=
  Classical.propDecidable _

/-! ## Chords and alignment -/

/-- A chord on the circle, given by an ordered pair of endpoints (the underlying
chord is the unordered pair). -/
abbrev Chord (m : ℕ) := ZMod m × ZMod m

/-- The chord `A` separates the chords `B` and `C`: the endpoints of `B` are strictly
on one arc determined by `A` and the endpoints of `C` are strictly on the other.
(We use this only when the endpoints of `B` and `C` avoid those of `A`.) -/
def ChordSep {N : ℕ} [NeZero N] (A B C : Chord N) : Prop :=
  (sbtw A.1 B.1 A.2 ∧ sbtw A.1 B.2 A.2 ∧ ¬ sbtw A.1 C.1 A.2 ∧ ¬ sbtw A.1 C.2 A.2) ∨
  (¬ sbtw A.1 B.1 A.2 ∧ ¬ sbtw A.1 B.2 A.2 ∧ sbtw A.1 C.1 A.2 ∧ sbtw A.1 C.2 A.2)

/-- A family of chords is aligned if for any three distinct chords, one separates
the other two. -/
def ChordAligned {N : ℕ} [NeZero N] (F : Finset (Chord N)) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, ∀ C ∈ F, A ≠ B → B ≠ C → A ≠ C →
    ChordSep A B C ∨ ChordSep B A C ∨ ChordSep C A B

/-- A family of chords is pairwise non-crossing if any two distinct chords do not
cross, i.e. the endpoints of the second are on the same arc determined by the
first. -/
def ChordNonCrossing {N : ℕ} [NeZero N] (F : Finset (Chord N)) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, A ≠ B → (sbtw A.1 B.1 A.2 ↔ sbtw A.1 B.2 A.2)

/-- A family of chords is pairwise vertex-disjoint. -/
def ChordDisjoint {N : ℕ} [NeZero N] (F : Finset (Chord N)) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, A ≠ B → A.1 ≠ B.1 ∧ A.1 ≠ B.2 ∧ A.2 ≠ B.1 ∧ A.2 ≠ B.2

/-- The family of `k`-chords of an arrangement `σ` of `[0, N - 1]`: pairs of
positions `(σ x, σ y)` with `x.val + y.val = k` and `x.val ≤ y.val` (so every
chord appears exactly once, including the degenerate chord with `2x = k`). -/
def kChords {N : ℕ} [NeZero N] (σ : ZMod N ≃ ZMod N) (k : ℕ) :
    Finset (Chord N) :=
  ((Finset.univ ×ˢ Finset.univ).filter fun p : ZMod N × ZMod N =>
    p.1.val + p.2.val = k ∧ p.1.val ≤ p.2.val).image fun p => (σ p.1, σ p.2)

theorem mem_kChords {N : ℕ} [NeZero N] {σ : ZMod N ≃ ZMod N} {k : ℕ} {A : Chord N} :
    A ∈ kChords σ k ↔ ∃ x y : ZMod N, x.val + y.val = k ∧ x.val ≤ y.val ∧
      A = (σ x, σ y) := by
  unfold kChords
  rw [Finset.mem_image]
  constructor
  · rintro ⟨p, hp, rfl⟩
    rw [Finset.mem_filter, Finset.mem_product] at hp
    exact ⟨p.1, p.2, hp.2.1, hp.2.2, rfl⟩
  · rintro ⟨x, y, hsum, hle, rfl⟩
    exact ⟨(x, y), by rw [Finset.mem_filter, Finset.mem_product]; exact ⟨⟨Finset.mem_univ x,
      Finset.mem_univ y⟩, hsum, hle⟩, rfl⟩

/-- The `k`-chords are pairwise vertex-disjoint. -/
theorem kChords_disjoint {N : ℕ} [NeZero N] {σ : ZMod N ≃ ZMod N} {k : ℕ} :
    ChordDisjoint (kChords σ k) := by
  intro A hA B hB hne
  rw [mem_kChords] at hA hB
  obtain ⟨xa, ya, hsa, hlea, rfl⟩ := hA
  obtain ⟨xb, yb, hsb, hleb, rfl⟩ := hB
  have hsum : xa.val + ya.val = xb.val + yb.val := by omega
  have key : ∀ u v u' v' : ℕ, u + v = u' + v' → u ≤ v → u' ≤ v' →
      (u = u' ∧ v = v') ∨ (u ≠ u' ∧ u ≠ v' ∧ v ≠ u' ∧ v ≠ v') := by
    intro u v u' v' h hle hle'
    by_cases huu' : u = u'
    · exact Or.inl ⟨huu', by omega⟩
    · by_cases huv' : u = v'
      · have hv : v = u' := by omega
        have : u = u' := by omega
        exact absurd this huu'
      · by_cases hvu' : v = u'
        · have hv : v' = u := by omega
          have : u = u' := by omega
          exact absurd this huu'
        · exact Or.inr ⟨huu', huv', hvu', by omega⟩
  obtain ⟨h1, h2⟩ | ⟨h1, h2, h3, h4⟩ := key xa.val ya.val xb.val yb.val hsum hlea hleb
  · have e1 : xa = xb := ZMod.val_injective _ h1
    have e2 : ya = yb := ZMod.val_injective _ h2
    subst e1; subst e2
    exact absurd rfl hne
  · exact ⟨fun h => h1 (congrArg ZMod.val (σ.injective h)),
      fun h => h2 (congrArg ZMod.val (σ.injective h)),
      fun h => h3 (congrArg ZMod.val (σ.injective h)),
      fun h => h4 (congrArg ZMod.val (σ.injective h))⟩

/-- For distinct points, strict betweenness flips under reversal. -/
theorem sbtw_not_reverse {N : ℕ} [NeZero N] {a b c : ZMod N} (ha : a ≠ b) (hb : b ≠ c)
    (hc : c ≠ a) : sbtw a b c ↔ ¬ sbtw c b a := by
  refine ⟨sbtw_asymm, fun h => ?_⟩
  rcases btw_total a b c with hbt | hbt
  · apply sbtw_of_btw_not_btw hbt
    intro hbt'
    obtain h1 | h1 | h1 := hbt.antisymm hbt'
    · exact ha h1
    · exact hb h1
    · exact hc h1
  · exfalso
    apply h
    apply sbtw_of_btw_not_btw hbt
    intro hbt'
    obtain h1 | h1 | h1 := hbt.antisymm hbt'
    · exact hb h1.symm
    · exact ha h1.symm
    · exact hc h1.symm

/-! ## Structure theorem for aligned chord families

A pairwise non-crossing, pairwise vertex-disjoint, aligned family of chords on
`ZMod (m + 1)` that covers every point and has at most one degenerate chord has
all chord endpoint-sums equal to a constant (`const_sum_of_aligned`). Ported from
a standalone development, using the circular-order and chord infrastructure of
this file. -/

theorem val_natCast_of_lt {n : ℕ} {k : ℕ} (hk : k < n + 1) : ((k : ZMod (n + 1))).val = k := by
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt hk]

theorem val_one' {n : ℕ} (hn : 1 ≤ n) : (1 : ZMod (n + 1)).val = 1 := by
  have e : (1 : ZMod (n + 1)) = ((1 : ℕ) : ZMod (n + 1)) := by rw [Nat.cast_one]
  rw [e, val_natCast_of_lt (by omega)]

/-- Value of `-(k)` for a nat cast `k`. -/
theorem val_neg_natCast {n : ℕ} {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    (-(k : ZMod (n + 1))).val = n + 1 - k := by
  have e : (-(k : ZMod (n + 1))) = ((n + 1 - k : ℕ) : ZMod (n + 1)) := by
    rw [neg_eq_iff_add_eq_zero, ← Nat.cast_add]
    have h : k + (n + 1 - k) = n + 1 := by omega
    rw [h, ZMod.natCast_self]
  rw [e, val_natCast_of_lt (by omega)]

/-- Betweenness via differences. -/
theorem btw_val {n : ℕ} {a b c : ZMod (n + 1)} (hac : a ≠ c) :
    btw a b c ↔ (b - a).val ≤ (c - a).val := by
  rw [btw_zmod_def, val_sub' b a, val_sub' c a]
  have ha := ZMod.val_lt a
  have hac' : a.val ≠ c.val := fun h => hac (ZMod.val_injective _ h)
  have key : ∀ x : ZMod (n + 1), (x.val + (n + 1) - a.val) % (n + 1) =
      if a.val ≤ x.val then x.val - a.val else x.val + (n + 1) - a.val := by
    intro x
    have hxl := ZMod.val_lt x
    by_cases hx : a.val ≤ x.val
    · rw [if_pos hx]
      have e : x.val + (n + 1) - a.val = (x.val - a.val) + (n + 1) := by omega
      rw [e, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : x.val - a.val < n + 1)]
    · rw [if_neg hx, Nat.mod_eq_of_lt (by omega : x.val + (n + 1) - a.val < n + 1)]
  rw [key b, key c]
  have hb := ZMod.val_lt b; have hc := ZMod.val_lt c
  by_cases h1 : a.val ≤ b.val <;> by_cases h2 : a.val ≤ c.val <;> simp [h1, h2] <;> omega

/-- A point distinct from `a` and `c` lies on one of the two open arcs. -/
theorem sbtw_or_sbtw_rev {m : ℕ} {a b c : ZMod (m + 1)} (hba : b ≠ a) (hbc : b ≠ c)
    (hac : a ≠ c) : sbtw a b c ∨ sbtw c b a := by
  by_contra h
  push Not at h
  have h2 := sbtw_not_reverse hba.symm hbc hac.symm
  exact h.1 (h2.2 h.2)

/-- `sbtw` implies pairwise distinctness. -/
theorem sbtw_ne {m : ℕ} {a b c : ZMod (m + 1)} (h : sbtw a b c) :
    a ≠ b ∧ b ≠ c ∧ a ≠ c := by
  rw [sbtw_zmod_def] at h
  refine ⟨?_, ?_, ?_⟩ <;> intro he <;> subst he <;> omega

/-- Subtraction by `t` preserves strict betweenness. -/
theorem sbtw_sub {n : ℕ} {a b c : ZMod (n + 1)} (t : ZMod (n + 1)) (hab : a ≠ b) :
    sbtw (a - t) (b - t) (c - t) ↔ sbtw a b c := by
  have h := sbtw_add (-t) hab (a := a) (b := b) (c := c)
  simpa [sub_eq_add_neg] using h

/-- `ChordSep` is invariant under simultaneous translation of all endpoints. -/
theorem ChordSep_sub {m : ℕ} {A₁ A₂ B₁ B₂ C₁ C₂ : ZMod (m + 1)} (t : ZMod (m + 1))
    (hAB1 : A₁ ≠ B₁) (hAB2 : A₁ ≠ B₂) (hAC1 : A₁ ≠ C₁) (hAC2 : A₁ ≠ C₂) :
    ChordSep (A₁ - t, A₂ - t) (B₁ - t, B₂ - t) (C₁ - t, C₂ - t) ↔
    ChordSep (A₁, A₂) (B₁, B₂) (C₁, C₂) := by
  unfold ChordSep
  rw [sbtw_sub t hAB1, sbtw_sub t hAB2, sbtw_sub t hAC1, sbtw_sub t hAC2]

/-- Three chords whose endpoints come in a strict chain `Rt, a, q, r, b, L` along the
circle (measured by values relative to `Rt`) are not aligned, whatever the
orientations of the chords. -/
theorem not_aligned_of_chain_rel {m : ℕ} {C0 B C : Chord (m + 1)} {L Rt a q r b : ZMod (m + 1)}
    (hC0 : (C0.1 = Rt ∧ C0.2 = L) ∨ (C0.1 = L ∧ C0.2 = Rt))
    (hB : (B.1 = a ∧ B.2 = q) ∨ (B.1 = q ∧ B.2 = a))
    (hC : (C.1 = b ∧ C.2 = r) ∨ (C.1 = r ∧ C.2 = b))
    (ha : (a - Rt).val = 1)
    (h1 : 1 < (q - Rt).val) (h2 : (q - Rt).val < (r - Rt).val)
    (h3 : (r - Rt).val < (b - Rt).val) (h4 : (b - Rt).val < (L - Rt).val)
    (halign : ChordSep C0 B C ∨ ChordSep B C0 C ∨ ChordSep C C0 B) : False := by
  -- pairwise distinctness of the six points, from the chain
  have v0 : (Rt - Rt).val = 0 := by rw [sub_self]; rfl
  have d : ∀ x y : ZMod (m + 1), (x - Rt).val ≠ (y - Rt).val → x ≠ y :=
    fun x y h he => h (by rw [he])
  have naq : a ≠ q := d a q (by rw [ha]; omega)
  have nar : a ≠ r := d a r (by rw [ha]; omega)
  have nab : a ≠ b := d a b (by rw [ha]; omega)
  have naL : a ≠ L := d a L (by rw [ha]; omega)
  have nqr : q ≠ r := d q r (by omega)
  have nqb : q ≠ b := d q b (by omega)
  have nqL : q ≠ L := d q L (by omega)
  have nrb : r ≠ b := d r b (by omega)
  have nrL : r ≠ L := d r L (by omega)
  have nbL : b ≠ L := d b L (by omega)
  have naRt : a ≠ Rt := d a Rt (by rw [ha, v0]; omega)
  have nqRt : q ≠ Rt := d q Rt (by rw [v0]; omega)
  have nrRt : r ≠ Rt := d r Rt (by rw [v0]; omega)
  have nbRt : b ≠ Rt := d b Rt (by rw [v0]; omega)
  have nLRt : L ≠ Rt := d L Rt (by rw [v0]; omega)
  -- shift the alignment disjunction by `-Rt` and finish by `omega`
  rcases hC0 with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rcases hB with ⟨e3, e4⟩ | ⟨e3, e4⟩ <;>
    rcases hC with ⟨e5, e6⟩ | ⟨e5, e6⟩ <;> simp only [ChordSep] at halign <;> rw [e1, e2, e3, e4, e5, e6] at halign <;>
    rcases halign with h | h | h
  · have hT := (ChordSep_sub Rt naRt.symm nqRt.symm nbRt.symm nrRt.symm).2 h
    rw [sub_self Rt] at hT
    simp only [ChordSep, sbtw_zmod_def, ZMod.val_zero] at hT
    omega
  · have hT := (ChordSep_sub Rt naRt naL nab nar).2 h
    rw [sub_self Rt] at hT
    simp only [ChordSep, sbtw_zmod_def, ZMod.val_zero] at hT
    omega
  · have hT := (ChordSep_sub Rt nbRt nbL nab.symm nqb.symm).2 h
    rw [sub_self Rt] at hT
    simp only [ChordSep, sbtw_zmod_def, ZMod.val_zero] at hT
    omega
  · have hT := (ChordSep_sub Rt naRt.symm nqRt.symm nrRt.symm nbRt.symm).2 h
    rw [sub_self Rt] at hT
    simp only [ChordSep, sbtw_zmod_def, ZMod.val_zero] at hT
    omega
  · have hT := (ChordSep_sub Rt naRt naL nar nab).2 h
    rw [sub_self Rt] at hT
    simp only [ChordSep, sbtw_zmod_def, ZMod.val_zero] at hT
    omega
  · have hT := (ChordSep_sub Rt nrRt nrL nar.symm nqr.symm).2 h
    rw [sub_self Rt] at hT
    simp only [ChordSep, sbtw_zmod_def, ZMod.val_zero] at hT
    omega
  · have hT := (ChordSep_sub Rt nqRt.symm naRt.symm nbRt.symm nrRt.symm).2 h
    rw [sub_self Rt] at hT
    simp only [ChordSep, sbtw_zmod_def, ZMod.val_zero] at hT
    omega
  · have hT := (ChordSep_sub Rt nqRt nqL nqb nqr).2 h
    rw [sub_self Rt] at hT
    simp only [ChordSep, sbtw_zmod_def, ZMod.val_zero] at hT
    omega
  · have hT := (ChordSep_sub Rt nbRt nbL nqb.symm nab.symm).2 h
    rw [sub_self Rt] at hT
    simp only [ChordSep, sbtw_zmod_def, ZMod.val_zero] at hT
    omega
  · have hT := (ChordSep_sub Rt nqRt.symm naRt.symm nrRt.symm nbRt.symm).2 h
    rw [sub_self Rt] at hT
    simp only [ChordSep, sbtw_zmod_def, ZMod.val_zero] at hT
    omega
  · have hT := (ChordSep_sub Rt nqRt nqL nqr nqb).2 h
    rw [sub_self Rt] at hT
    simp only [ChordSep, sbtw_zmod_def, ZMod.val_zero] at hT
    omega
  · have hT := (ChordSep_sub Rt nrRt nrL nqr.symm nar.symm).2 h
    rw [sub_self Rt] at hT
    simp only [ChordSep, sbtw_zmod_def, ZMod.val_zero] at hT
    omega
  · have hT := (ChordSep_sub Rt naL.symm nqL.symm nbL.symm nrL.symm).2 h
    rw [sub_self Rt] at hT
    simp only [ChordSep, sbtw_zmod_def, ZMod.val_zero] at hT
    omega
  · have hT := (ChordSep_sub Rt naL naRt nab nar).2 h
    rw [sub_self Rt] at hT
    simp only [ChordSep, sbtw_zmod_def, ZMod.val_zero] at hT
    omega
  · have hT := (ChordSep_sub Rt nbL nbRt nab.symm nqb.symm).2 h
    rw [sub_self Rt] at hT
    simp only [ChordSep, sbtw_zmod_def, ZMod.val_zero] at hT
    omega
  · have hT := (ChordSep_sub Rt naL.symm nqL.symm nrL.symm nbL.symm).2 h
    rw [sub_self Rt] at hT
    simp only [ChordSep, sbtw_zmod_def, ZMod.val_zero] at hT
    omega
  · have hT := (ChordSep_sub Rt naL naRt nar nab).2 h
    rw [sub_self Rt] at hT
    simp only [ChordSep, sbtw_zmod_def, ZMod.val_zero] at hT
    omega
  · have hT := (ChordSep_sub Rt nrL nrRt nar.symm nqr.symm).2 h
    rw [sub_self Rt] at hT
    simp only [ChordSep, sbtw_zmod_def, ZMod.val_zero] at hT
    omega
  · have hT := (ChordSep_sub Rt nqL.symm naL.symm nbL.symm nrL.symm).2 h
    rw [sub_self Rt] at hT
    simp only [ChordSep, sbtw_zmod_def, ZMod.val_zero] at hT
    omega
  · have hT := (ChordSep_sub Rt nqL nqRt nqb nqr).2 h
    rw [sub_self Rt] at hT
    simp only [ChordSep, sbtw_zmod_def, ZMod.val_zero] at hT
    omega
  · have hT := (ChordSep_sub Rt nbL nbRt nqb.symm nab.symm).2 h
    rw [sub_self Rt] at hT
    simp only [ChordSep, sbtw_zmod_def, ZMod.val_zero] at hT
    omega
  · have hT := (ChordSep_sub Rt nqL.symm naL.symm nrL.symm nbL.symm).2 h
    rw [sub_self Rt] at hT
    simp only [ChordSep, sbtw_zmod_def, ZMod.val_zero] at hT
    omega
  · have hT := (ChordSep_sub Rt nqL nqRt nqr nqb).2 h
    rw [sub_self Rt] at hT
    simp only [ChordSep, sbtw_zmod_def, ZMod.val_zero] at hT
    omega
  · have hT := (ChordSep_sub Rt nrL nrRt nqr.symm nar.symm).2 h
    rw [sub_self Rt] at hT
    simp only [ChordSep, sbtw_zmod_def, ZMod.val_zero] at hT
    omega

/-- Degenerate-second-chord variant of `not_aligned_of_chain_rel`. -/
theorem not_aligned_of_chain_rel_degB {m : ℕ} {C0 B C : Chord (m + 1)} {L Rt a r b : ZMod (m + 1)}
    (hC0 : (C0.1 = Rt ∧ C0.2 = L) ∨ (C0.1 = L ∧ C0.2 = Rt))
    (hB : B.1 = a ∧ B.2 = a)
    (hC : (C.1 = b ∧ C.2 = r) ∨ (C.1 = r ∧ C.2 = b))
    (ha : (a - Rt).val = 1)
    (h2 : 1 < (r - Rt).val) (h3 : (r - Rt).val < (b - Rt).val) (h4 : (b - Rt).val < (L - Rt).val)
    (halign : ChordSep C0 B C ∨ ChordSep B C0 C ∨ ChordSep C C0 B) : False := by
  have v0 : (Rt - Rt).val = 0 := by rw [sub_self]; rfl
  have d : ∀ x y : ZMod (m + 1), (x - Rt).val ≠ (y - Rt).val → x ≠ y :=
    fun x y h he => h (by rw [he])
  have nar : a ≠ r := d a r (by rw [ha]; omega)
  have nab : a ≠ b := d a b (by rw [ha]; omega)
  have naL : a ≠ L := d a L (by rw [ha]; omega)
  have nrb : r ≠ b := d r b (by omega)
  have nrL : r ≠ L := d r L (by omega)
  have nbL : b ≠ L := d b L (by omega)
  have naRt : a ≠ Rt := d a Rt (by rw [ha, v0]; omega)
  have nrRt : r ≠ Rt := d r Rt (by rw [v0]; omega)
  have nbRt : b ≠ Rt := d b Rt (by rw [v0]; omega)
  have nLRt : L ≠ Rt := d L Rt (by rw [v0]; omega)
  obtain ⟨e3, e4⟩ := hB
  rcases hC0 with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rcases hC with ⟨e5, e6⟩ | ⟨e5, e6⟩ <;>
    simp only [ChordSep] at halign <;> rw [e1, e2, e3, e4, e5, e6] at halign <;>
    rcases halign with h | h | h
  · have hT := (ChordSep_sub Rt naRt.symm naRt.symm nbRt.symm nrRt.symm).2 h
    rw [sub_self Rt] at hT
    simp only [ChordSep, sbtw_zmod_def, ZMod.val_zero] at hT
    omega
  · have hT := (ChordSep_sub Rt naRt naL nab nar).2 h
    rw [sub_self Rt] at hT
    simp only [ChordSep, sbtw_zmod_def, ZMod.val_zero] at hT
    omega
  · have hT := (ChordSep_sub Rt nbRt nbL nab.symm nab.symm).2 h
    rw [sub_self Rt] at hT
    simp only [ChordSep, sbtw_zmod_def, ZMod.val_zero] at hT
    omega
  · have hT := (ChordSep_sub Rt naRt.symm naRt.symm nrRt.symm nbRt.symm).2 h
    rw [sub_self Rt] at hT
    simp only [ChordSep, sbtw_zmod_def, ZMod.val_zero] at hT
    omega
  · have hT := (ChordSep_sub Rt naRt naL nar nab).2 h
    rw [sub_self Rt] at hT
    simp only [ChordSep, sbtw_zmod_def, ZMod.val_zero] at hT
    omega
  · have hT := (ChordSep_sub Rt nrRt nrL nar.symm nar.symm).2 h
    rw [sub_self Rt] at hT
    simp only [ChordSep, sbtw_zmod_def, ZMod.val_zero] at hT
    omega
  · have hT := (ChordSep_sub Rt naL.symm naL.symm nbL.symm nrL.symm).2 h
    rw [sub_self Rt] at hT
    simp only [ChordSep, sbtw_zmod_def, ZMod.val_zero] at hT
    omega
  · have hT := (ChordSep_sub Rt naL naRt nab nar).2 h
    rw [sub_self Rt] at hT
    simp only [ChordSep, sbtw_zmod_def, ZMod.val_zero] at hT
    omega
  · have hT := (ChordSep_sub Rt nbL nbRt nab.symm nab.symm).2 h
    rw [sub_self Rt] at hT
    simp only [ChordSep, sbtw_zmod_def, ZMod.val_zero] at hT
    omega
  · have hT := (ChordSep_sub Rt naL.symm naL.symm nrL.symm nbL.symm).2 h
    rw [sub_self Rt] at hT
    simp only [ChordSep, sbtw_zmod_def, ZMod.val_zero] at hT
    omega
  · have hT := (ChordSep_sub Rt naL naRt nar nab).2 h
    rw [sub_self Rt] at hT
    simp only [ChordSep, sbtw_zmod_def, ZMod.val_zero] at hT
    omega
  · have hT := (ChordSep_sub Rt nrL nrRt nar.symm nar.symm).2 h
    rw [sub_self Rt] at hT
    simp only [ChordSep, sbtw_zmod_def, ZMod.val_zero] at hT
    omega

/-- Degenerate-third-chord variant of `not_aligned_of_chain_rel`. -/
theorem not_aligned_of_chain_rel_degC {m : ℕ} {C0 B C : Chord (m + 1)} {L Rt a q b : ZMod (m + 1)}
    (hC0 : (C0.1 = Rt ∧ C0.2 = L) ∨ (C0.1 = L ∧ C0.2 = Rt))
    (hB : (B.1 = a ∧ B.2 = q) ∨ (B.1 = q ∧ B.2 = a))
    (hC : C.1 = b ∧ C.2 = b)
    (ha : (a - Rt).val = 1)
    (h2 : 1 < (q - Rt).val) (h3 : (q - Rt).val < (b - Rt).val) (h4 : (b - Rt).val < (L - Rt).val)
    (halign : ChordSep C0 B C ∨ ChordSep B C0 C ∨ ChordSep C C0 B) : False := by
  have v0 : (Rt - Rt).val = 0 := by rw [sub_self]; rfl
  have d : ∀ x y : ZMod (m + 1), (x - Rt).val ≠ (y - Rt).val → x ≠ y :=
    fun x y h he => h (by rw [he])
  have naq : a ≠ q := d a q (by rw [ha]; omega)
  have nab : a ≠ b := d a b (by rw [ha]; omega)
  have naL : a ≠ L := d a L (by rw [ha]; omega)
  have nqb : q ≠ b := d q b (by omega)
  have nqL : q ≠ L := d q L (by omega)
  have nbL : b ≠ L := d b L (by omega)
  have naRt : a ≠ Rt := d a Rt (by rw [ha, v0]; omega)
  have nqRt : q ≠ Rt := d q Rt (by rw [v0]; omega)
  have nbRt : b ≠ Rt := d b Rt (by rw [v0]; omega)
  have nLRt : L ≠ Rt := d L Rt (by rw [v0]; omega)
  obtain ⟨e5, e6⟩ := hC
  rcases hC0 with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rcases hB with ⟨e3, e4⟩ | ⟨e3, e4⟩ <;>
    simp only [ChordSep] at halign <;> rw [e1, e2, e3, e4, e5, e6] at halign <;>
    rcases halign with h | h | h
  · have hT := (ChordSep_sub Rt naRt.symm nqRt.symm nbRt.symm nbRt.symm).2 h
    rw [sub_self Rt] at hT
    simp only [ChordSep, sbtw_zmod_def, ZMod.val_zero] at hT
    omega
  · have hT := (ChordSep_sub Rt naRt naL nab nab).2 h
    rw [sub_self Rt] at hT
    simp only [ChordSep, sbtw_zmod_def, ZMod.val_zero] at hT
    omega
  · have hT := (ChordSep_sub Rt nbRt nbL nab.symm nqb.symm).2 h
    rw [sub_self Rt] at hT
    simp only [ChordSep, sbtw_zmod_def, ZMod.val_zero] at hT
    omega
  · have hT := (ChordSep_sub Rt nqRt.symm naRt.symm nbRt.symm nbRt.symm).2 h
    rw [sub_self Rt] at hT
    simp only [ChordSep, sbtw_zmod_def, ZMod.val_zero] at hT
    omega
  · have hT := (ChordSep_sub Rt nqRt nqL nqb nqb).2 h
    rw [sub_self Rt] at hT
    simp only [ChordSep, sbtw_zmod_def, ZMod.val_zero] at hT
    omega
  · have hT := (ChordSep_sub Rt nbRt nbL nqb.symm nab.symm).2 h
    rw [sub_self Rt] at hT
    simp only [ChordSep, sbtw_zmod_def, ZMod.val_zero] at hT
    omega
  · have hT := (ChordSep_sub Rt naL.symm nqL.symm nbL.symm nbL.symm).2 h
    rw [sub_self Rt] at hT
    simp only [ChordSep, sbtw_zmod_def, ZMod.val_zero] at hT
    omega
  · have hT := (ChordSep_sub Rt naL naRt nab nab).2 h
    rw [sub_self Rt] at hT
    simp only [ChordSep, sbtw_zmod_def, ZMod.val_zero] at hT
    omega
  · have hT := (ChordSep_sub Rt nbL nbRt nab.symm nqb.symm).2 h
    rw [sub_self Rt] at hT
    simp only [ChordSep, sbtw_zmod_def, ZMod.val_zero] at hT
    omega
  · have hT := (ChordSep_sub Rt nqL.symm naL.symm nbL.symm nbL.symm).2 h
    rw [sub_self Rt] at hT
    simp only [ChordSep, sbtw_zmod_def, ZMod.val_zero] at hT
    omega
  · have hT := (ChordSep_sub Rt nqL nqRt nqb nqb).2 h
    rw [sub_self Rt] at hT
    simp only [ChordSep, sbtw_zmod_def, ZMod.val_zero] at hT
    omega
  · have hT := (ChordSep_sub Rt nbL nbRt nqb.symm nab.symm).2 h
    rw [sub_self Rt] at hT
    simp only [ChordSep, sbtw_zmod_def, ZMod.val_zero] at hT
    omega

/-- In a non-crossing disjoint family, if one endpoint of `B` lies on the `Rt → L`
open arc determined by `A`'s endpoints `{L, Rt}`, so does the other endpoint. -/
theorem far_transfer {m : ℕ} {F : Finset (Chord (m + 1))} (hnc : ChordNonCrossing F)
    (hdj : ChordDisjoint F) {A B : Chord (m + 1)} (hA : A ∈ F) (hB : B ∈ F) (hne : A ≠ B)
    {L Rt p q : ZMod (m + 1)}
    (hAe : (A.1 = Rt ∧ A.2 = L) ∨ (A.1 = L ∧ A.2 = Rt))
    (hBe : (B.1 = p ∧ B.2 = q) ∨ (B.1 = q ∧ B.2 = p))
    (hLR : L ≠ Rt) (hp : sbtw Rt p L) : sbtw Rt q L := by
  have hd := hdj A hA B hB hne
  have hnc' := hnc A hA B hB hne
  have hpne := sbtw_ne hp
  rcases hAe with ⟨ha1, ha2⟩ | ⟨ha1, ha2⟩ <;> rcases hBe with ⟨hb1, hb2⟩ | ⟨hb1, hb2⟩ <;>
    rw [ha1, ha2, hb1, hb2] at hnc' hd
  · exact hnc'.1 hp
  · exact hnc'.2 hp
  · -- `A = (L, Rt)`, `B = (p, q)`: contrapose via reversal
    have h1 : ¬ sbtw L p Rt := (sbtw_not_reverse hpne.1 hpne.2.1 hLR).1 hp
    have h2 : ¬ sbtw L q Rt := fun hq => h1 (hnc'.2 hq)
    have hqL : q ≠ L := hd.2.1.symm
    have hqRt : q ≠ Rt := hd.2.2.2.symm
    rcases sbtw_or_sbtw_rev hqRt hqL hLR.symm with hq | hq
    · exact hq
    · exact absurd hq h2
  · have h1 : ¬ sbtw L p Rt := (sbtw_not_reverse hpne.1 hpne.2.1 hLR).1 hp
    have h2 : ¬ sbtw L q Rt := fun hq => h1 (hnc'.1 hq)
    have hqL : q ≠ L := hd.1.symm
    have hqRt : q ≠ Rt := hd.2.2.1.symm
    rcases sbtw_or_sbtw_rev hqRt hqL hLR.symm with hq | hq
    · exact hq
    · exact absurd hq h2

/-- The peeling invariant: after `i` peeling steps around the gap arc `(U, V)`, the
chords `c_j = {V+j, U-j}` for `j < i` are in `F`, every point of the closed arc
`[U-i+1, V+i-1]` is an endpoint of one of these chords or equals `R` (the point of
the unique degenerate chord, if present), `R` lies in the arc, and the arc has not
yet wrapped around the circle. -/
def PeelInv {m : ℕ} (F : Finset (Chord (m + 1))) (U V R : ZMod (m + 1)) (i : ℕ) : Prop :=
  (∀ j < i, ∃ B ∈ F, (B.1 = V + (j : ZMod (m + 1)) ∧ B.2 = U - (j : ZMod (m + 1))) ∨
      (B.1 = U - (j : ZMod (m + 1)) ∧ B.2 = V + (j : ZMod (m + 1)))) ∧
  (∀ p : ZMod (m + 1), btw (U - (i : ZMod (m + 1)) + 1) p (V + (i : ZMod (m + 1)) - 1) →
    (p = R ∨ ∃ j < i, p = V + (j : ZMod (m + 1)) ∨ p = U - (j : ZMod (m + 1)))) ∧
  (∀ j < i, (R, R) ∈ F → V + (j : ZMod (m + 1)) ≠ R ∧ U - (j : ZMod (m + 1)) ≠ R) ∧
  ((R, R) ∈ F ∨ R = V) ∧
  btw (U - (i : ZMod (m + 1)) + 1) R (V + (i : ZMod (m + 1)) - 1) ∧
  (V - U).val + 2 * i ≤ m + 2

/-- `btw` on a non-degenerate arc is an endpoint or strict betweenness. -/
theorem btw_eq_or_sbtw {m : ℕ} {a b c : ZMod (m + 1)} (h : btw a b c) (hac : a ≠ c) :
    b = a ∨ b = c ∨ sbtw a b c := by
  by_cases hba : b = a
  · exact Or.inl hba
  · by_cases hbc : b = c
    · exact Or.inr (Or.inl hbc)
    · refine Or.inr (Or.inr (sbtw_of_btw_not_btw h ?_))
      intro h'
      obtain e | e | e := h.antisymm h'
      · exact hba e.symm
      · exact hbc e
      · exact hac e.symm

/-- The peeling step: if the arc has at least two uncovered points, the chord through
the next point on the `V` side is forced to be `{V+i, U-i}`, extending the invariant. -/
theorem peel_step {m : ℕ} {F : Finset (Chord (m + 1))}
    (hnc : ChordNonCrossing F) (hdj : ChordDisjoint F) (hal : ChordAligned F)
    (hcov : ∀ p : ZMod (m + 1), ∃ A ∈ F, p = A.1 ∨ p = A.2)
    (hdeg : ∀ A ∈ F, ∀ B ∈ F, A.1 = A.2 → B.1 = B.2 → A = B)
    {U V R : ZMod (m + 1)} {i : ℕ} (hi : 1 ≤ i) (hUV1 : 1 ≤ (V - U).val)
    (hroom : (V - U).val + 2 * i ≤ m) (hinv : PeelInv F U V R i) :
    PeelInv F U V R (i + 1) := by
  obtain ⟨hI1, hI2, hI3, hI4, hI5, hI6⟩ := hinv
  set s := (V - U).val with hs
  set Rt : ZMod (m + 1) := V + (i : ZMod (m + 1)) - 1 with hRt
  set L : ZMod (m + 1) := U - (i : ZMod (m + 1)) + 1 with hL
  set a : ZMod (m + 1) := V + (i : ZMod (m + 1)) with ha
  set b : ZMod (m + 1) := U - (i : ZMod (m + 1)) with hb
  have hm : 3 ≤ m := by omega
  -- the previous chord `c_{i-1}` has endpoints `{Rt, L}`
  obtain ⟨C0, hC0F, hC0e⟩ := hI1 (i - 1) (by omega)
  have eRt : V + ((i - 1 : ℕ) : ZMod (m + 1)) = Rt := by
    rw [hRt, ha, Nat.cast_sub hi, Nat.cast_one]; ring
  have eL : U - ((i - 1 : ℕ) : ZMod (m + 1)) = L := by
    rw [hL, hb, Nat.cast_sub hi, Nat.cast_one]; ring
  rw [eRt, eL] at hC0e
  -- val identities
  have hcast : ∀ k : ℕ, (V - U) + (k : ZMod (m + 1)) = ((s + k : ℕ) : ZMod (m + 1)) := by
    intro k
    have e : ((s : ZMod (m + 1))) = V - U := by rw [hs, ZMod.natCast_zmod_val]
    rw [Nat.cast_add, e]
  have hRtL : (Rt - L).val = s + 2 * i - 2 := by
    have e : Rt - L = (V - U) + ((2 * i - 2 : ℕ) : ZMod (m + 1)) := by
      rw [hRt, hL, ha, hb, Nat.cast_sub (by omega : 2 ≤ 2 * i)]; push_cast; ring
    rw [e, hcast, val_natCast_of_lt (by omega)]; omega
  have haRt : (a - Rt).val = 1 := by
    have e : a - Rt = 1 := by rw [hRt]; ring
    rw [e, val_one' (by omega : 1 ≤ m)]
  have hbRt : (b - Rt).val = m + 1 - (s + 2 * i - 1) := by
    have e : b - Rt = -(((s + (2 * i - 1) : ℕ)) : ZMod (m + 1)) := by
      have e1 : (V - U) + ((2 * i - 1 : ℕ) : ZMod (m + 1)) = ((s + (2 * i - 1) : ℕ) : ZMod (m + 1)) := hcast _
      have e2 : b - Rt = -((V - U) + ((2 * i - 1 : ℕ) : ZMod (m + 1))) := by
        rw [hb, hRt, ha, Nat.cast_sub (by omega : 1 ≤ 2 * i)]; push_cast; ring
      rw [e2, e1]
    rw [e, val_neg_natCast (by omega : 1 ≤ s + (2 * i - 1)) (by omega : s + (2 * i - 1) ≤ m)]; omega
  have hLRt : (L - Rt).val = m + 1 - (s + 2 * i - 2) := by
    have e : L - Rt = -(((s + (2 * i - 2) : ℕ)) : ZMod (m + 1)) := by
      have e1 : Rt - L = ((s + (2 * i - 2) : ℕ) : ZMod (m + 1)) := by
        have e2 : Rt - L = (V - U) + ((2 * i - 2 : ℕ) : ZMod (m + 1)) := by
          rw [hRt, hL, ha, hb, Nat.cast_sub (by omega : 2 ≤ 2 * i)]; push_cast; ring
        rw [e2, hcast]
      rw [show L - Rt = -(Rt - L) from by ring, e1]
    rw [e, val_neg_natCast (by omega : 1 ≤ s + (2 * i - 2)) (by omega : s + (2 * i - 2) ≤ m)]; omega
  have haL : (a - L).val = s + 2 * i - 1 := by
    have e : a - L = (V - U) + ((2 * i - 1 : ℕ) : ZMod (m + 1)) := by
      rw [ha, hL, hb, Nat.cast_sub (by omega : 1 ≤ 2 * i)]; push_cast; ring
    rw [e, hcast, val_natCast_of_lt (by omega)]; omega
  have hbL : (b - L).val = m := by
    have e : b - L = -1 := by rw [hL]; ring
    rw [e]
    have e1 : (-1 : ZMod (m + 1)) = -((1 : ℕ) : ZMod (m + 1)) := by rw [Nat.cast_one]
    rw [e1, val_neg_natCast (le_refl 1) (by omega : 1 ≤ m)]
    omega
  have hab : (a - b).val = s + 2 * i := by
    have e : a - b = (V - U) + ((2 * i : ℕ) : ZMod (m + 1)) := by rw [ha, hb]; push_cast; ring
    rw [e, hcast, val_natCast_of_lt (by omega)]
  -- distinctness
  have LRt : L ≠ Rt := by
    intro he; rw [he, sub_self] at hRtL; simp at hRtL; omega
  have aRt : a ≠ Rt := by
    intro he; rw [he, sub_self] at haRt; simp at haRt
  have bRt : b ≠ Rt := by
    intro he; rw [he, sub_self] at hbRt; simp at hbRt; omega
  have aL : a ≠ L := by
    intro he; rw [he, sub_self] at haL; simp at haL; omega
  have bL : b ≠ L := by
    intro he; rw [he, sub_self] at hbL; simp at hbL; omega
  have ab : a ≠ b := by
    intro he; rw [he, sub_self] at hab; simp at hab; omega
  -- arc membership of the fresh points
  have ha_far : sbtw Rt a L := by
    rw [sbtw_val aRt.symm, haRt, hLRt]; omega
  have hb_far : sbtw Rt b L := by
    rw [sbtw_val bRt.symm, hbRt, hLRt]; omega
  have ha_narc : ¬ btw L a Rt := by
    rw [btw_val LRt, haL, hRtL]; omega
  have hb_narc : ¬ btw L b Rt := by
    rw [btw_val LRt, hbL, hRtL]; omega
  -- cover `a`
  obtain ⟨B, hBF, hBa⟩ := hcov a
  have hBC0 : C0 ≠ B := by
    intro he
    rw [← he] at hBa
    rcases hC0e with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2] at hBa
    · rcases hBa with h | h
      · exact aRt h
      · exact aL h
    · rcases hBa with h | h
      · exact aL h
      · exact aRt h
  obtain ⟨q, hBq⟩ : ∃ q, (B.1 = a ∧ B.2 = q) ∨ (B.1 = q ∧ B.2 = a) := by
    rcases hBa with h | h
    · exact ⟨B.2, Or.inl ⟨h.symm, rfl⟩⟩
    · exact ⟨B.1, Or.inr ⟨rfl, h.symm⟩⟩
  have hq_far : sbtw Rt q L := far_transfer hnc hdj hC0F hBF hBC0 hC0e hBq LRt ha_far
  have hqne := sbtw_ne hq_far
  rw [sbtw_val hqne.1, hLRt] at hq_far
  -- `hq_far : (q - Rt).val < m + 1 - (s + 2*i - 2)`
  by_cases hqa : q = a
  · -- `B` degenerate (impossible, via the alignment triple)
    have hBeq : B.1 = a ∧ B.2 = a := by
      rcases hBq with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · exact ⟨e1, by rw [e2, hqa]⟩
      · exact ⟨by rw [e1, hqa], e2⟩
    obtain ⟨C, hCF, hCb⟩ := hcov b
    have hCC0 : C0 ≠ C := by
      intro he
      rw [← he] at hCb
      rcases hC0e with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2] at hCb
      · rcases hCb with h | h
        · exact bRt h
        · exact bL h
      · rcases hCb with h | h
        · exact bL h
        · exact bRt h
    have hCB : B ≠ C := by
      intro he
      rw [← he] at hCb
      rcases hCb with h | h
      · exact ab (by rw [h, hBeq.1])
      · exact ab (by rw [h, hBeq.2])
    by_cases hCdeg : C.1 = C.2
    · exact absurd (hdeg B hBF C hCF (by rw [hBeq.1, hBeq.2]) hCdeg) hCB
    · obtain ⟨r, hCr⟩ : ∃ r, (C.1 = b ∧ C.2 = r) ∨ (C.1 = r ∧ C.2 = b) := by
        rcases hCb with h | h
        · exact ⟨C.2, Or.inl ⟨h.symm, rfl⟩⟩
        · exact ⟨C.1, Or.inr ⟨rfl, h.symm⟩⟩
      have hr : r ≠ b := by
        rcases hCr with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · intro he; exact hCdeg (by rw [e1, e2, he])
        · intro he; exact hCdeg (by rw [e1, e2, ← he])
      have hr_far : sbtw Rt r L := far_transfer hnc hdj hC0F hCF hCC0 hC0e hCr LRt hb_far
      have hrne := sbtw_ne hr_far
      rw [sbtw_val hrne.1, hLRt] at hr_far
      have hra : r ≠ a := by
        have hd := hdj B hBF C hCF hCB
        rcases hCr with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2, hBeq.1, hBeq.2] at hd
        · exact hd.2.2.2.symm
        · exact hd.2.2.1.symm
      have hvr0 : 1 ≤ (r - Rt).val := by
        rcases Nat.eq_zero_or_pos (r - Rt).val with hz | hz
        · exfalso; apply hrne.1
          have e : r - Rt = 0 := by
            have e2 := ZMod.natCast_zmod_val (r - Rt)
            rw [hz, Nat.cast_zero] at e2
            exact e2.symm
          rw [sub_eq_zero] at e; exact e.symm
        · exact hz
      have hvr1 : 1 < (r - Rt).val := by
        rcases eq_or_ne (r - Rt).val 1 with hz | hz
        · exfalso; apply hra
          have e : r - Rt = a - Rt := ZMod.val_injective _ (by rw [hz, haRt])
          exact sub_left_injective e
        · omega
      have hvr2 : (r - Rt).val < (b - Rt).val := by
        have hne : (r - Rt).val ≠ (b - Rt).val := fun hz => hr (sub_left_injective (ZMod.val_injective _ hz))
        omega
      have hb_far' : (b - Rt).val < (L - Rt).val := by
        rw [sbtw_val bRt.symm] at hb_far; exact hb_far
      exact (not_aligned_of_chain_rel_degB hC0e hBeq hCr haRt hvr1 hvr2 hb_far'
        (hal C0 hC0F B hBF C hCF hBC0 hCB hCC0)).elim
  · by_cases hqb : q = b
    · -- success: `B = {a, b}` is the new chord `c_i`
      rw [hqb] at hBq
      refine ⟨?_, ?_, ?_, hI4, ?_, by omega⟩
      · intro j hj
        rcases eq_or_lt_of_le (by omega : j ≤ i) with hje | hje
        · rw [hje]
          exact ⟨B, hBF, by rw [← ha, ← hb]; exact hBq⟩
        · exact hI1 j hje
      · intro p hp
        have e1 : U - ((i + 1 : ℕ) : ZMod (m + 1)) + 1 = b := by
          rw [hb, Nat.cast_add, Nat.cast_one]; ring
        have e2 : V + ((i + 1 : ℕ) : ZMod (m + 1)) - 1 = a := by
          rw [ha, Nat.cast_add, Nat.cast_one]; ring
        rw [e1, e2] at hp
        rcases btw_eq_or_sbtw hp ab.symm with hpb | hpa | hp'
        · exact Or.inr ⟨i, by omega, Or.inr (by rw [hpb, hb])⟩
        · exact Or.inr ⟨i, by omega, Or.inl (by rw [hpa, ha])⟩
        · -- `p` strictly between `b` and `a`: in the old arc
          have hpne := sbtw_ne hp'
          have hpL : btw L p Rt := by
            rw [btw_val LRt]
            rw [sbtw_val hpne.1, hab] at hp'
            have hpb1 : 1 ≤ (p - b).val := by
              rcases Nat.eq_zero_or_pos (p - b).val with hz | hz
              · exfalso; apply hpne.1
                have e : p - b = 0 := by
                  have e2 := ZMod.natCast_zmod_val (p - b)
                  rw [hz, Nat.cast_zero] at e2
                  exact e2.symm
                rw [sub_eq_zero] at e; exact e.symm
              · exact hz
            have e3 : p - L = (p - b) - 1 := by rw [hL]; ring
            have e4 : (p - L).val = (p - b).val - 1 := by
              rw [e3]
              have e5 : (p - b) - 1 = (((p - b).val - 1 : ℕ) : ZMod (m + 1)) := by
                rw [Nat.cast_sub hpb1, Nat.cast_one, ZMod.natCast_zmod_val]
              rw [e5, val_natCast_of_lt (by have := ZMod.val_lt (p - b); omega)]
            rw [e4, hRtL]; omega
          rcases hI2 p hpL with hpR | ⟨j, hj, hjp⟩
          · exact Or.inl hpR
          · exact Or.inr ⟨j, by omega, hjp⟩
      · intro j hj hRR
        rcases eq_or_lt_of_le (by omega : j ≤ i) with hje | hje
        · rw [hje]
          have haR : a ≠ R := by
            intro he
            rw [he] at ha_narc
            exact ha_narc (by rw [← he] at hI5 ⊢; exact hI5)
          have hbR : b ≠ R := by
            intro he
            rw [he] at hb_narc
            exact hb_narc (by rw [← he] at hI5 ⊢; exact hI5)
          rw [← ha]
          exact ⟨haR, by rw [← hb]; exact hbR⟩
        · exact hI3 j hje hRR
      · have e1 : U - ((i + 1 : ℕ) : ZMod (m + 1)) + 1 = b := by
          rw [hb, Nat.cast_add, Nat.cast_one]; ring
        have e2 : V + ((i + 1 : ℕ) : ZMod (m + 1)) - 1 = a := by
          rw [ha, Nat.cast_add, Nat.cast_one]; ring
        rw [e1, e2, btw_val ab.symm, hab]
        have hRL : (R - L).val ≤ s + 2 * i - 2 := by
          rw [btw_val LRt, hRtL] at hI5; exact hI5
        have e3 : R - b = (R - L) + 1 := by rw [hL]; ring
        have e4 : (R - b).val = (R - L).val + 1 := by
          rw [e3]
          have e5 : (R - L) + 1 = (((R - L).val + 1 : ℕ) : ZMod (m + 1)) := by
            have e6 := ZMod.natCast_zmod_val (R - L)
            rw [Nat.cast_add, Nat.cast_one, e6]
          rw [e5, val_natCast_of_lt (by have := ZMod.val_lt (R - L); omega)]
        rw [e4]; omega
    · -- the generic case is impossible (alignment triple)
      obtain ⟨C, hCF, hCb⟩ := hcov b
      have hCC0 : C0 ≠ C := by
        intro he
        rw [← he] at hCb
        rcases hC0e with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2] at hCb
        · rcases hCb with h | h
          · exact bRt h
          · exact bL h
        · rcases hCb with h | h
          · exact bL h
          · exact bRt h
      have hCB : B ≠ C := by
        intro he
        rw [← he] at hCb
        rcases hBq with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2] at hCb
        · rcases hCb with h | h
          · exact ab h.symm
          · exact hqb h.symm
        · rcases hCb with h | h
          · exact hqb h.symm
          · exact ab h.symm
      have hvq0 : 1 ≤ (q - Rt).val := by
        rcases Nat.eq_zero_or_pos (q - Rt).val with hz | hz
        · exfalso; apply hqne.1
          have e : q - Rt = 0 := by
            have e2 := ZMod.natCast_zmod_val (q - Rt)
            rw [hz, Nat.cast_zero] at e2
            exact e2.symm
          rw [sub_eq_zero] at e; exact e.symm
        · exact hz
      have hvq1 : 1 < (q - Rt).val := by
        rcases eq_or_ne (q - Rt).val 1 with hz | hz
        · exfalso; apply hqa
          have e : q - Rt = a - Rt := ZMod.val_injective _ (by rw [hz, haRt])
          exact sub_left_injective e
        · omega
      by_cases hCdeg : C.1 = C.2
      · -- `C` degenerate: impossible
        have hCeq : C.1 = b ∧ C.2 = b := by
          rcases hCb with h | h
          · exact ⟨h.symm, (hCdeg ▸ h).symm⟩
          · exact ⟨(hCdeg.symm ▸ h).symm, h.symm⟩
        have hvb2 : (q - Rt).val < (b - Rt).val := by
          have hne : (q - Rt).val ≠ (b - Rt).val := fun hz => hqb (sub_left_injective (ZMod.val_injective _ hz))
          omega
        have hb_far' : (b - Rt).val < (L - Rt).val := by
          rw [sbtw_val bRt.symm] at hb_far; exact hb_far
        exact (not_aligned_of_chain_rel_degC hC0e hBq hCeq haRt hvq1 hvb2 hb_far'
          (hal C0 hC0F B hBF C hCF hBC0 hCB hCC0)).elim
      · obtain ⟨r, hCr⟩ : ∃ r, (C.1 = b ∧ C.2 = r) ∨ (C.1 = r ∧ C.2 = b) := by
          rcases hCb with h | h
          · exact ⟨C.2, Or.inl ⟨h.symm, rfl⟩⟩
          · exact ⟨C.1, Or.inr ⟨rfl, h.symm⟩⟩
        have hr : r ≠ b := by
          rcases hCr with ⟨e1, e2⟩ | ⟨e1, e2⟩
          · intro he; exact hCdeg (by rw [e1, e2, he])
          · intro he; exact hCdeg (by rw [e1, e2, ← he])
        have hr_far : sbtw Rt r L := far_transfer hnc hdj hC0F hCF hCC0 hC0e hCr LRt hb_far
        have hrne := sbtw_ne hr_far
        rw [sbtw_val hrne.1, hLRt] at hr_far
        have hdBC := hdj B hBF C hCF hCB
        have hBC := hnc B hBF C hCF hCB
        -- value conversions relative to `Rt`
        have hid : ∀ x y : ZMod (m + 1), (x - Rt).val < (y - Rt).val →
            ((y - x).val = (y - Rt).val - (x - Rt).val) := by
          intro x y hxy
          have e : y - x = (((y - Rt).val - (x - Rt).val : ℕ) : ZMod (m + 1)) := by
            have e1 := ZMod.natCast_zmod_val (y - Rt)
            have e2 := ZMod.natCast_zmod_val (x - Rt)
            have e3 : y - x = (y - Rt) - (x - Rt) := by ring
            rw [e3, Nat.cast_sub (by omega : (x - Rt).val ≤ (y - Rt).val), e1, e2]
          rw [e, val_natCast_of_lt (by have := ZMod.val_lt (y - Rt); have := ZMod.val_lt (x - Rt); omega)]
        have hid1 : ∀ x : ZMod (m + 1), 1 ≤ (x - Rt).val →
            ((x - a).val = (x - Rt).val - 1) := by
          intro x hx
          have e : x - a = (((x - Rt).val - 1 : ℕ) : ZMod (m + 1)) := by
            have e1 := ZMod.natCast_zmod_val (x - Rt)
            have e2 : x - a = (x - Rt) - 1 := by rw [hRt]; ring
            rw [e2, Nat.cast_sub hx, Nat.cast_one, e1]
          rw [e, val_natCast_of_lt (by have := ZMod.val_lt (x - Rt); omega)]
        have hid2 : ∀ x : ZMod (m + 1), 2 ≤ (x - Rt).val →
            ((a - x).val = m + 1 - ((x - Rt).val - 1)) := by
          intro x hx
          have e : a - x = -(((x - Rt).val - 1 : ℕ) : ZMod (m + 1)) := by
            have e1 : x - a = (((x - Rt).val - 1 : ℕ) : ZMod (m + 1)) := by
              have e2 := ZMod.natCast_zmod_val (x - Rt)
              have e3 : x - a = (x - Rt) - 1 := by rw [hRt]; ring
              rw [e3, Nat.cast_sub (by omega : 1 ≤ (x - Rt).val), Nat.cast_one, e2]
            rw [show a - x = -(x - a) from by ring, e1]
          rw [e, val_neg_natCast (by omega : 1 ≤ (x - Rt).val - 1)
            (by have := ZMod.val_lt (x - Rt); omega : (x - Rt).val - 1 ≤ m)]
        have hvr0 : 1 ≤ (r - Rt).val := by
          rcases Nat.eq_zero_or_pos (r - Rt).val with hz | hz
          · exfalso; apply hrne.1
            have e : r - Rt = 0 := by
              have e2 := ZMod.natCast_zmod_val (r - Rt)
              rw [hz, Nat.cast_zero] at e2
              exact e2.symm
            rw [sub_eq_zero] at e; exact e.symm
          · exact hz
        have hra : r ≠ a := by
          rcases hBq with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rcases hCr with ⟨e3, e4⟩ | ⟨e3, e4⟩ <;>
            rw [e1, e2, e3, e4] at hdBC
          · exact hdBC.2.1.symm
          · exact hdBC.1.symm
          · exact hdBC.2.2.2.symm
          · exact hdBC.2.2.1.symm
        have hrq : r ≠ q := by
          rcases hBq with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rcases hCr with ⟨e3, e4⟩ | ⟨e3, e4⟩ <;>
            rw [e1, e2, e3, e4] at hdBC
          · exact hdBC.2.2.2.symm
          · exact hdBC.2.2.1.symm
          · exact hdBC.2.1.symm
          · exact hdBC.1.symm
        have hvr1 : (r - Rt).val ≠ 1 := by
          intro hz
          apply hra
          have e : r - Rt = a - Rt := ZMod.val_injective _ (by rw [hz, haRt])
          exact sub_left_injective e
        have hvrq : (r - Rt).val ≠ (q - Rt).val := fun hz => hrq (sub_left_injective (ZMod.val_injective _ hz))
        -- `sbtw a b q` and `sbtw a r q`
        have hba_conv : (b - a).val = m + 1 - (s + 2 * i) := by
          have e : b - a = -(((s + 2 * i : ℕ)) : ZMod (m + 1)) := by
            have e1 : a - b = ((s + 2 * i : ℕ) : ZMod (m + 1)) := by
              have e2 : a - b = (V - U) + ((2 * i : ℕ) : ZMod (m + 1)) := by rw [ha, hb]; push_cast; ring
              rw [e2, hcast]
            rw [show b - a = -(a - b) from by ring, e1]
          rw [e, val_neg_natCast (by omega : 1 ≤ s + 2 * i) (by omega : s + 2 * i ≤ m)]
        -- the chain `(q - Rt).val < (r - Rt).val` from non-crossing of `B` and `C`
        have hqr : (q - Rt).val < (r - Rt).val := by
          have hvq2 : 2 ≤ (q - Rt).val := by omega
          have hvr2 : 2 ≤ (r - Rt).val := by omega
          have hvb2 : 2 ≤ (b - Rt).val := by omega
          have hqbv : (q - Rt).val < (b - Rt).val := by
            have hne : (q - Rt).val ≠ (b - Rt).val := fun hz =>
              hqb (sub_left_injective (ZMod.val_injective _ hz))
            omega
          have hTra : ∀ x y : ZMod (m + 1), 2 ≤ (x - Rt).val → 2 ≤ (y - Rt).val →
              (sbtw a x y ↔ (x - Rt).val < (y - Rt).val) := by
            intro x y hx hy
            have e1 : a - Rt = 1 := by rw [hRt]; ring
            have h1x : (1 : ZMod (m + 1)) ≠ x - Rt := by
              intro he
              rw [← he, val_one' (by omega : 1 ≤ m)] at hx
              omega
            have habx : a ≠ x := by
              intro he
              rw [← he, e1] at h1x
              exact h1x rfl
            rw [← sbtw_sub Rt habx, e1, sbtw_val h1x,
              show x - Rt - 1 = x - a from by rw [hRt]; ring,
              show y - Rt - 1 = y - a from by rw [hRt]; ring,
              hid1 x (by omega : 1 ≤ (x - Rt).val), hid1 y (by omega : 1 ≤ (y - Rt).val)]
            constructor <;> intro h' <;> omega
          have hTrq : ∀ x : ZMod (m + 1), 2 ≤ (x - Rt).val → q ≠ x →
              (sbtw q x a ↔ (q - Rt).val < (x - Rt).val) := by
            intro x hx hqx
            have h1 : q - Rt ≠ x - Rt := fun he => hqx (sub_left_injective he)
            have e1 : a - Rt = 1 := by rw [hRt]; ring
            rw [← sbtw_sub Rt hqx, e1, sbtw_val h1]
            have h2 : ((x - Rt) - (q - Rt)).val = if (q - Rt).val ≤ (x - Rt).val then
                (x - Rt).val - (q - Rt).val else (x - Rt).val + (m + 1) - (q - Rt).val := by
              have e3 : (x - Rt) - (q - Rt) =
                  (((x - Rt).val : ℕ) : ZMod (m + 1)) - (((q - Rt).val : ℕ) : ZMod (m + 1)) := by
                have e4 := ZMod.natCast_zmod_val (x - Rt)
                have e5 := ZMod.natCast_zmod_val (q - Rt)
                rw [e4, e5]
              rw [e3, val_sub_if]
              rw [val_natCast_of_lt (by have := ZMod.val_lt (x - Rt); omega : (x - Rt).val < m + 1),
                val_natCast_of_lt (by have := ZMod.val_lt (q - Rt); omega : (q - Rt).val < m + 1)]
            have h3 : (1 - (q - Rt)).val = m + 2 - (q - Rt).val := by
              have e3 : (1 : ZMod (m + 1)) - (q - Rt) = a - q := by rw [hRt]; ring
              rw [e3, hid2 q hvq1]
              omega
            have hne : (q - Rt).val ≠ (x - Rt).val := fun hz => h1 (ZMod.val_injective _ hz)
            have hlt : (q - Rt).val < m + 1 := ZMod.val_lt _
            have hlt' : (x - Rt).val < m + 1 := ZMod.val_lt _
            rw [h2, h3]
            split_ifs with hle
            · constructor <;> intro h' <;> omega
            · constructor <;> intro h' <;> omega
          rcases hBq with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rcases hCr with ⟨e3, e4⟩ | ⟨e3, e4⟩ <;>
            rw [e1, e2, e3, e4] at hBC
          · rw [hTra b q hvb2 hvq2, hTra r q hvr2 hvq2] at hBC
            omega
          · rw [hTra r q hvr2 hvq2, hTra b q hvb2 hvq2] at hBC
            omega
          · rw [hTrq b hvb2 hqb, hTrq r hvr2 hrq.symm] at hBC
            omega
          · rw [hTrq r hvr2 hrq.symm, hTrq b hvb2 hqb] at hBC
            omega
        have hrb_val : (r - Rt).val < (b - Rt).val := by
          have hne : (r - Rt).val ≠ (b - Rt).val := fun hz =>
            hr (sub_left_injective (ZMod.val_injective _ hz))
          omega
        have hb_far' : (b - Rt).val < (L - Rt).val := by
          rw [sbtw_val bRt.symm] at hb_far; exact hb_far
        exact (not_aligned_of_chain_rel hC0e hBq hCr haRt hvq1 hqr hrb_val hb_far'
          (hal C0 hC0F B hBF C hCF hBC0 hCB hCC0)).elim

/-- Two chords of a vertex-disjoint family that share an endpoint are equal. -/
theorem eq_of_shared_endpoint {m : ℕ} {F : Finset (Chord (m + 1))} (hdj : ChordDisjoint F)
    {A B : Chord (m + 1)} (hA : A ∈ F) (hB : B ∈ F) {p : ZMod (m + 1)}
    (hpA : p = A.1 ∨ p = A.2) (hpB : p = B.1 ∨ p = B.2) : A = B := by
  by_contra hne
  have hd := hdj A hA B hB hne
  rcases hpA with hpA | hpA <;> rcases hpB with hpB | hpB
  · exact hd.1 (hpA.symm.trans hpB)
  · exact hd.2.1 (hpA.symm.trans hpB)
  · exact hd.2.2.1 (hpA.symm.trans hpB)
  · exact hd.2.2.2 (hpA.symm.trans hpB)

/-- Finalization: once the arc covers the whole circle (up to one point), every chord
of the family has endpoint sum `U + V`. -/
theorem peel_final {m : ℕ} {F : Finset (Chord (m + 1))}
    (_hnc : ChordNonCrossing F) (hdj : ChordDisjoint F) (_hal : ChordAligned F)
    (_hcov : ∀ p : ZMod (m + 1), ∃ A ∈ F, p = A.1 ∨ p = A.2)
    (_hdeg : ∀ A ∈ F, ∀ B ∈ F, A.1 = A.2 → B.1 = B.2 → A = B)
    {U V R : ZMod (m + 1)} {i : ℕ} (hi : 1 ≤ i) (hUV1 : 1 ≤ (V - U).val)
    (hfull : m + 1 ≤ (V - U).val + 2 * i) (hinv : PeelInv F U V R i) :
    ∀ A ∈ F, A.1 + A.2 = U + V := by
  obtain ⟨hI1, hI2, hI3, hI4, hI5, hI6⟩ := hinv
  intro A hAF
  set s := (V - U).val with hs
  set L : ZMod (m + 1) := U - (i : ZMod (m + 1)) + 1 with hL
  set Rt : ZMod (m + 1) := V + (i : ZMod (m + 1)) - 1 with hRt
  have hm : 1 ≤ m := by omega
  have hcast : ∀ k : ℕ, (V - U) + (k : ZMod (m + 1)) = ((s + k : ℕ) : ZMod (m + 1)) := by
    intro k
    have e : ((s : ZMod (m + 1))) = V - U := by rw [hs, ZMod.natCast_zmod_val]
    rw [Nat.cast_add, e]
  have hRtL : (Rt - L).val = s + 2 * i - 2 := by
    have e : Rt - L = (V - U) + ((2 * i - 2 : ℕ) : ZMod (m + 1)) := by
      rw [hRt, hL, Nat.cast_sub (by omega : 2 ≤ 2 * i)]; push_cast; ring
    rw [e, hcast, val_natCast_of_lt (by omega)]; omega
  have LRt : L ≠ Rt := by
    intro he; rw [he, sub_self] at hRtL; simp at hRtL; omega
  have hLval : (L - Rt).val = m + 1 - (s + 2 * i - 2) := by
    have e : L - Rt = -(((s + (2 * i - 2) : ℕ)) : ZMod (m + 1)) := by
      have e1 : Rt - L = ((s + (2 * i - 2) : ℕ) : ZMod (m + 1)) := by
        have e2 : Rt - L = (V - U) + ((2 * i - 2 : ℕ) : ZMod (m + 1)) := by
          rw [hRt, hL, Nat.cast_sub (by omega : 2 ≤ 2 * i)]; push_cast; ring
        rw [e2, hcast]
      rw [show L - Rt = -(Rt - L) from by ring, e1]
    rw [e, val_neg_natCast (by omega : 1 ≤ s + (2 * i - 2)) (by omega : s + (2 * i - 2) ≤ m)]
    omega
  -- endpoints of the `c_j` chords lie in the arc
  have hmem : ∀ j < i, btw L (V + (j : ZMod (m + 1))) Rt ∧ btw L (U - (j : ZMod (m + 1))) Rt := by
    intro j hj
    have e1 : V + (j : ZMod (m + 1)) - L = (V - U) + ((i + j - 1 : ℕ) : ZMod (m + 1)) := by
      rw [hL, Nat.cast_sub (by omega : 1 ≤ i + j)]; push_cast; ring
    have e2 : (V + (j : ZMod (m + 1)) - L).val = s + (i + j - 1) := by
      rw [e1, hcast, val_natCast_of_lt (by omega)]
    have e3 : U - (j : ZMod (m + 1)) - L = (((i - j - 1 : ℕ)) : ZMod (m + 1)) := by
      have h1 : ((i - j - 1 : ℕ) : ZMod (m + 1)) = (i : ZMod (m + 1)) - (j : ZMod (m + 1)) - 1 := by
        have hcs : ((i - j - 1 : ℕ) : ZMod (m + 1)) = ((i - j : ℕ) : ZMod (m + 1)) - 1 :=
          Nat.cast_sub (by omega : 1 ≤ i - j)
        have hcs2 : ((i - j : ℕ) : ZMod (m + 1)) = (i : ZMod (m + 1)) - (j : ZMod (m + 1)) :=
          Nat.cast_sub (by omega : j ≤ i)
        rw [hcs, hcs2]
      rw [hL, h1]; ring
    have e4 : (U - (j : ZMod (m + 1)) - L).val = i - j - 1 := by
      rw [e3, val_natCast_of_lt (by omega)]
    rw [btw_val LRt, e2, hRtL]
    refine ⟨by omega, ?_⟩
    rw [btw_val LRt, e4, hRtL]
    omega
  -- point classification: everything is in the arc or equals `W := Rt + 1`
  set W : ZMod (m + 1) := Rt + 1 with hW
  have hclass : ∀ p : ZMod (m + 1), btw L p Rt ∨ p = W := by
    intro p
    by_cases h : btw L p Rt
    · exact Or.inl h
    · right
      have hRt_p : Rt ≠ p := by
        intro he
        exact h (by rw [← he]; exact (btw_val LRt).2 (le_refl _))
      have h2 : sbtw Rt p L :=
        of_not_not (fun hs => h ((btw_iff_not_sbtw (a := L) (b := p) (c := Rt)).2 hs))
      rw [sbtw_val hRt_p, hLval] at h2
      have h3 : (p - Rt).val = 1 := by
        have h4 : (p - Rt).val ≠ 0 := by
          intro hz
          apply hRt_p
          have e : p - Rt = 0 := by
            have e2 := ZMod.natCast_zmod_val (p - Rt)
            rw [hz, Nat.cast_zero] at e2
            exact e2.symm
          rw [sub_eq_zero] at e
          exact e.symm
        omega
      have h5 : p - Rt = 1 := ZMod.val_injective _ (by rw [h3, val_one' hm])
      have h6 : p = Rt + 1 := by linear_combination h5
      rw [h6, hW]
  -- reflection: the degenerate chord's sum is also `U + V`
  have hRefl : (R, R) ∈ F → R + R = U + V := by
    intro hRR
    have hpt : ∀ p : ZMod (m + 1), p = R ∨
        (∃ j < i, p = V + (j : ZMod (m + 1)) ∨ p = U - (j : ZMod (m + 1))) ∨ p = W := by
      intro p
      rcases hclass p with hp | hp
      · rcases hI2 p hp with hpR | hj
        · exact Or.inl hpR
        · exact Or.inr (Or.inl hj)
      · exact Or.inr (Or.inr hp)
    rcases hpt (U + V - R) with h | h | h
    · linear_combination -h
    · obtain ⟨j, hj, hjv⟩ := h
      have hRne := hI3 j hj hRR
      rcases hjv with hjv | hjv
      · exfalso; apply hRne.2; linear_combination hjv
      · exfalso; apply hRne.1; linear_combination hjv
    · -- `U + V - R = W`: then `R = U - i`, fresh, contradiction
      exfalso
      have hRi : R = U - (i : ZMod (m + 1)) := by
        have hW' : W = V + (i : ZMod (m + 1)) := by rw [hW, hRt]; ring
        rw [hW'] at h
        linear_combination -h
      by_cases hs2 : s + 2 * i = m + 2
      · have hRi2 : R = V + ((i - 1 : ℕ) : ZMod (m + 1)) := by
          have e : (V - U) + 2 * (i : ZMod (m + 1)) = 1 := by
            have h2 : ((s + 2 * i : ℕ) : ZMod (m + 1)) = 1 := by
              rw [show s + 2 * i = 1 + (m + 1) from by omega, Nat.cast_add, ZMod.natCast_self,
                Nat.cast_one]
              ring
            rw [← hcast] at h2
            rw [show (2 : ZMod (m + 1)) * (i : ZMod (m + 1)) = ((2 * i : ℕ) : ZMod (m + 1)) from by
              push_cast; ring]
            exact h2
          rw [hRi]
          have e2 : V + ((i - 1 : ℕ) : ZMod (m + 1)) = V + ((i : ZMod (m + 1)) - 1) := by
            rw [Nat.cast_sub hi, Nat.cast_one]
          rw [e2]
          linear_combination -e
        exact (hI3 (i - 1) (by omega) hRR).1 hRi2.symm
      · have hnfresh : ¬ btw L (U - (i : ZMod (m + 1))) Rt := by
          rw [btw_val LRt, hRtL]
          have e : U - (i : ZMod (m + 1)) - L = -1 := by rw [hL]; ring
          rw [e]
          have e1 : (-1 : ZMod (m + 1)) = -((1 : ℕ) : ZMod (m + 1)) := by rw [Nat.cast_one]
          rw [e1, val_neg_natCast (le_refl 1) (by omega : 1 ≤ m)]
          omega
        rw [hRi] at hI5
        exact hnfresh hI5
  -- every chord with an endpoint in the arc is a `c_j` or the degenerate chord
  have hchord : ∀ B ∈ F, ∀ p : ZMod (m + 1), (p = B.1 ∨ p = B.2) → btw L p Rt →
      (∃ j < i, (B.1 = V + (j : ZMod (m + 1)) ∧ B.2 = U - (j : ZMod (m + 1))) ∨
        (B.1 = U - (j : ZMod (m + 1)) ∧ B.2 = V + (j : ZMod (m + 1)))) ∨ B = (R, R) := by
    intro B hBF p hp hpbt
    rcases hI2 p hpbt with hpR | ⟨j, hj, hjp⟩
    · by_cases hRR : (R, R) ∈ F
      · exact Or.inr (eq_of_shared_endpoint hdj hBF hRR hp (Or.inl hpR))
      · have hRV : R = V := hI4.resolve_left hRR
        obtain ⟨B', hB'F, hB'e⟩ := hI1 0 (by omega)
        have hpB' : p = B'.1 ∨ p = B'.2 := by
          have hpV : p = V := by rw [hRV] at hpR; exact hpR
          rcases hB'e with ⟨e1, e2⟩ | ⟨e1, e2⟩
          · rw [e1]
            exact Or.inl (by rw [hpV, Nat.cast_zero, add_zero])
          · rw [e2]
            exact Or.inr (by rw [hpV, Nat.cast_zero, add_zero])
        have hBB' := eq_of_shared_endpoint hdj hBF hB'F hp hpB'
        exact Or.inl ⟨0, by omega, by rw [hBB']; exact hB'e⟩
    · obtain ⟨B', hB'F, hB'e⟩ := hI1 j hj
      have hpB' : p = B'.1 ∨ p = B'.2 := by
        rcases hB'e with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · rcases hjp with hjp | hjp
          · exact Or.inl (by rw [e1]; exact hjp)
          · exact Or.inr (by rw [e2]; exact hjp)
        · rcases hjp with hjp | hjp
          · exact Or.inr (by rw [e2]; exact hjp)
          · exact Or.inl (by rw [e1]; exact hjp)
      have hBB' := eq_of_shared_endpoint hdj hBF hB'F hp hpB'
      exact Or.inl ⟨j, hj, by rw [hBB']; exact hB'e⟩
  -- case split: `A.1` in the arc or not
  by_cases hA1 : btw L A.1 Rt
  · rcases hchord A hAF A.1 (Or.inl rfl) hA1 with ⟨j, hj, hje⟩ | hAD
    · rcases hje with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2] <;> ring
    · rw [hAD]
      have hRR : (R, R) ∈ F := by rw [hAD] at hAF; exact hAF
      exact hRefl hRR
  · -- `A.1 = W`, and then also `A.2 = W`
    have hA1W : A.1 = W := (hclass A.1).resolve_left hA1
    have hWnarc : ¬ btw L W Rt := by rw [hA1W] at hA1; exact hA1
    have hsm : s + 2 * i = m + 1 := by
      by_contra hs2
      have hs3 : s + 2 * i = m + 2 := by omega
      have hRtLm : (Rt - L).val = m := by omega
      have hWL : W = L := by
        have e : W - L = 1 + (Rt - L) := by rw [hW]; ring
        have e2 : W - L = 0 := by
          have e3 : W - L = (((1 + (Rt - L).val : ℕ)) : ZMod (m + 1)) := by
            rw [e, Nat.cast_add, Nat.cast_one, ZMod.natCast_zmod_val]
          rw [e3]
          have e4 : 1 + (Rt - L).val = m + 1 := by omega
          rw [e4, ZMod.natCast_self]
        rw [sub_eq_zero] at e2
        exact e2
      rw [hWL] at hWnarc
      exact hWnarc ((btw_val LRt).2 (by simp))
    have hA2W : A.2 = W := by
      by_cases hA2 : btw L A.2 Rt
      · exfalso
        rcases hchord A hAF A.2 (Or.inr rfl) hA2 with ⟨j, hj, hje⟩ | hAD
        · rcases hje with ⟨e1, e2⟩ | ⟨e1, e2⟩
          · rw [e1] at hA1W
            have hbt := (hmem j hj).1
            rw [hA1W] at hbt
            exact hWnarc hbt
          · rw [e1] at hA1W
            have hbt := (hmem j hj).2
            rw [hA1W] at hbt
            exact hWnarc hbt
        · have hbt : btw L R Rt := hI5
          rw [hAD] at hA1W
          have hA1W' : R = W := hA1W
          rw [hA1W'] at hbt
          exact hWnarc hbt
      · exact (hclass A.2).resolve_left hA2
    have hAeq : A = (W, W) := Prod.ext hA1W hA2W
    have hWW : W + W = U + V := by
      have hW' : W = V + (i : ZMod (m + 1)) := by rw [hW, hRt]; ring
      have hz : (V - U) + ((2 * i : ℕ) : ZMod (m + 1)) = 0 := by
        have h2 : ((s + 2 * i : ℕ) : ZMod (m + 1)) = 0 := by
          rw [show s + 2 * i = m + 1 from by omega, ZMod.natCast_self]
        rw [← hcast] at h2
        exact h2
      have h3 : W + W = (U + V) + ((V - U) + ((2 * i : ℕ) : ZMod (m + 1))) := by
        rw [hW']; push_cast; ring
      rw [h3, hz, add_zero]
    rw [hAeq]
    exact hWW

/-- The peeling argument: starting from the central configuration (the chord `{U, V}`
whose interior is covered by `R`), every chord of the family has sum `U + V`. -/
theorem peel {m : ℕ} {F : Finset (Chord (m + 1))}
    (hnc : ChordNonCrossing F) (hdj : ChordDisjoint F) (hal : ChordAligned F)
    (hcov : ∀ p : ZMod (m + 1), ∃ A ∈ F, p = A.1 ∨ p = A.2)
    (hdeg : ∀ A ∈ F, ∀ B ∈ F, A.1 = A.2 → B.1 = B.2 → A = B)
    {U V R : ZMod (m + 1)}
    (hUV1 : 1 ≤ (V - U).val) (_hUV2 : (V - U).val ≤ 2) (hRpos : (R - U).val ≤ (V - U).val)
    (hc0 : ∃ B ∈ F, (B.1 = V ∧ B.2 = U) ∨ (B.1 = U ∧ B.2 = V))
    (hint : ∀ p : ZMod (m + 1), sbtw U p V → p = R)
    (hR : (R, R) ∈ F ∨ R = V)
    (hRdj : (R, R) ∈ F → V ≠ R ∧ U ≠ R) :
    ∀ A ∈ F, A.1 + A.2 = U + V := by
  have hUV0 : U ≠ V := by
    intro he
    rw [he, sub_self, ZMod.val_zero] at hUV1
    omega
  have hbase : PeelInv F U V R 1 := by
    refine ⟨?_, ?_, ?_, hR, ?_, by have := ZMod.val_lt (V - U); omega⟩
    · intro j hj
      rw [Nat.lt_one_iff.1 hj]
      obtain ⟨B, hBF, hBe⟩ := hc0
      refine ⟨B, hBF, ?_⟩
      rw [Nat.cast_zero, add_zero, sub_zero]
      exact hBe
    · intro p hp
      rw [Nat.cast_one, sub_add_cancel, show V + 1 - 1 = V from by ring] at hp
      rcases btw_eq_or_sbtw hp hUV0 with h1 | h2 | h3
      · exact Or.inr ⟨0, by omega, Or.inr (by rw [h1, Nat.cast_zero, sub_zero])⟩
      · exact Or.inr ⟨0, by omega, Or.inl (by rw [h2, Nat.cast_zero, add_zero])⟩
      · exact Or.inl (hint p h3)
    · intro j hj hRR
      rw [Nat.lt_one_iff.1 hj, Nat.cast_zero, add_zero, sub_zero]
      exact hRdj hRR
    · rw [Nat.cast_one, sub_add_cancel, show V + 1 - 1 = V from by ring]
      exact (btw_val hUV0).2 hRpos
  have key : ∀ n : ℕ, ∀ i : ℕ, m + 2 - ((V - U).val + 2 * i) = n → 1 ≤ i →
      PeelInv F U V R i → ∀ A ∈ F, A.1 + A.2 = U + V := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n IH =>
      intro i hn hi hinv
      by_cases hf : m + 1 ≤ (V - U).val + 2 * i
      · exact peel_final hnc hdj hal hcov hdeg hi hUV1 hf hinv
      · have hroom : (V - U).val + 2 * i ≤ m := by omega
        have hinv' := peel_step hnc hdj hal hcov hdeg hi hUV1 hroom hinv
        exact IH (m + 2 - ((V - U).val + 2 * (i + 1))) (by omega) (i + 1) rfl (by omega) hinv'
  exact key (m + 2 - ((V - U).val + 2 * 1)) 1 rfl (le_refl 1) hbase

/-- The boundary-edge analysis: for a non-degenerate chord `A0` minimizing the
span `min ((A.2 - A.1).val) ((A.1 - A.2).val)` in a non-crossing, vertex-disjoint,
covering family with at most one degenerate chord, the span (in the minimizing
orientation `(P, Q)`) is either 1 (a boundary edge) or 2, in which case the unique
interior point is covered by the degenerate chord. -/
theorem boundary_analysis {m : ℕ} {F : Finset (Chord (m + 1))}
    (hnc : ChordNonCrossing F) (hdj : ChordDisjoint F)
    (hcov : ∀ p : ZMod (m + 1), ∃ A ∈ F, p = A.1 ∨ p = A.2)
    (hdeg : ∀ A ∈ F, ∀ B ∈ F, A.1 = A.2 → B.1 = B.2 → A = B)
    {A0 : Chord (m + 1)} (hA0F : A0 ∈ F) (_hA0ne : A0.1 ≠ A0.2)
    (hA0min : ∀ B ∈ F, B.1 ≠ B.2 → min (A0.2 - A0.1).val (A0.1 - A0.2).val ≤
      min (B.2 - B.1).val (B.1 - B.2).val)
    {P Q : ZMod (m + 1)} (hPQ : A0 = (P, Q) ∨ A0 = (Q, P))
    (hdPQ : (Q - P).val = min (A0.2 - A0.1).val (A0.1 - A0.2).val)
    (hd0 : 1 ≤ min (A0.2 - A0.1).val (A0.1 - A0.2).val) :
    (Q - P).val = 1 ∨ ((Q - P).val = 2 ∧ (P + 1, P + 1) ∈ F) := by
  -- a non-degenerate chord with an endpoint strictly inside the `(P, Q)` arc
  -- contradicts minimality
  have hmin : ∀ B ∈ F, B.1 ≠ B.2 → ∀ T : ZMod (m + 1), (T = B.1 ∨ T = B.2) →
      sbtw P T Q → False := by
    intro B hBF hBnd T hTp hTs
    have hTsne := sbtw_ne hTs
    have hBA0 : B ≠ A0 := by
      intro he
      rw [he] at hTp
      rcases hPQ with hPQe | hPQe
      · rw [hPQe] at hTp
        rcases hTp with h | h
        · exact hTsne.1 h.symm
        · exact hTsne.2.1 h
      · rw [hPQe] at hTp
        rcases hTp with h | h
        · exact hTsne.2.1 h
        · exact hTsne.1 h.symm
    obtain ⟨S, hBS⟩ : ∃ S, (B.1 = T ∧ B.2 = S) ∨ (B.1 = S ∧ B.2 = T) := by
      rcases hTp with h | h
      · exact ⟨B.2, Or.inl ⟨h.symm, rfl⟩⟩
      · exact ⟨B.1, Or.inr ⟨rfl, h.symm⟩⟩
    have hTS : T ≠ S := by
      rcases hBS with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · intro he; exact hBnd (by rw [e1, e2, he])
      · intro he; exact hBnd (by rw [e1, e2, ← he])
    have hSs : sbtw P S Q := by
      have hnc' := hnc A0 hA0F B hBF hBA0.symm
      rcases hPQ with hPQe | hPQe
      · rw [hPQe] at hnc'
        rcases hBS with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · rw [e1, e2] at hnc'
          exact hnc'.1 hTs
        · rw [e1, e2] at hnc'
          exact hnc'.2 hTs
      · rw [hPQe] at hnc'
        have hTrev : ¬ sbtw Q T P := (sbtw_not_reverse hTsne.1 hTsne.2.1 hTsne.2.2.symm).1 hTs
        have hSS : S ≠ P ∧ S ≠ Q := by
          have hd := hdj A0 hA0F B hBF hBA0.symm
          rw [hPQe] at hd
          rcases hBS with ⟨e1, e2⟩ | ⟨e1, e2⟩
          · rw [e1, e2] at hd
            exact ⟨hd.2.2.2.symm, hd.2.1.symm⟩
          · rw [e1, e2] at hd
            exact ⟨hd.2.2.1.symm, hd.1.symm⟩
        rcases hBS with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · rw [e1, e2] at hnc'
          have h1 : ¬ sbtw Q S P := fun hs => hTrev (hnc'.2 hs)
          rcases sbtw_or_sbtw_rev hSS.1 hSS.2 hTsne.2.2 with hs | hs
          · exact hs
          · exact absurd hs h1
        · rw [e1, e2] at hnc'
          have h1 : ¬ sbtw Q S P := fun hs => hTrev (hnc'.1 hs)
          rcases sbtw_or_sbtw_rev hSS.1 hSS.2 hTsne.2.2 with hs | hs
          · exact hs
          · exact absurd hs h1
    -- value bounds for the two endpoints
    have hTsne2 := sbtw_ne hSs
    have hTP : 1 ≤ (T - P).val ∧ (T - P).val < (Q - P).val := by
      rw [sbtw_val hTsne.1] at hTs
      refine ⟨?_, hTs⟩
      rcases Nat.eq_zero_or_pos (T - P).val with hz | hz
      · exfalso
        apply hTsne.1
        have e := ZMod.natCast_zmod_val (T - P)
        rw [hz, Nat.cast_zero] at e
        have e' : T - P = 0 := e.symm
        rw [sub_eq_zero] at e'
        exact e'.symm
      · exact hz
    have hSP : 1 ≤ (S - P).val ∧ (S - P).val < (Q - P).val := by
      rw [sbtw_val hTsne2.1] at hSs
      refine ⟨?_, hSs⟩
      rcases Nat.eq_zero_or_pos (S - P).val with hz | hz
      · exfalso
        apply hTsne2.1
        have e := ZMod.natCast_zmod_val (S - P)
        rw [hz, Nat.cast_zero] at e
        have e' : S - P = 0 := e.symm
        rw [sub_eq_zero] at e'
        exact e'.symm
      · exact hz
    -- one of the two orientations has a smaller span
    have hdB : min (B.2 - B.1).val (B.1 - B.2).val < (Q - P).val := by
      have hdif : (S - T).val = (S - P).val - (T - P).val ∨
          (T - S).val = (T - P).val - (S - P).val := by
        by_cases hle : (S - P).val ≤ (T - P).val
        · right
          have e : T - S = ((((T - P).val - (S - P).val : ℕ)) : ZMod (m + 1)) := by
            have e1 := ZMod.natCast_zmod_val (T - P)
            have e2 := ZMod.natCast_zmod_val (S - P)
            have e3 : T - S = (T - P) - (S - P) := by ring
            rw [e3, Nat.cast_sub hle, e1, e2]
          rw [e, val_natCast_of_lt (by have := ZMod.val_lt (T - P); omega)]
        · left
          have e : S - T = ((((S - P).val - (T - P).val : ℕ)) : ZMod (m + 1)) := by
            have e1 := ZMod.natCast_zmod_val (S - P)
            have e2 := ZMod.natCast_zmod_val (T - P)
            have e3 : S - T = (S - P) - (T - P) := by ring
            rw [e3, Nat.cast_sub (by omega : (T - P).val ≤ (S - P).val), e1, e2]
          rw [e, val_natCast_of_lt (by have := ZMod.val_lt (S - P); omega)]
      rcases hdif with h | h
      · have hlt : (S - T).val < (Q - P).val := by omega
        rcases hBS with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · rw [e1, e2]
          exact lt_of_le_of_lt (min_le_left _ _) hlt
        · rw [e1, e2]
          exact lt_of_le_of_lt (min_le_right _ _) hlt
      · have hlt : (T - S).val < (Q - P).val := by omega
        rcases hBS with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · rw [e1, e2]
          exact lt_of_le_of_lt (min_le_right _ _) hlt
        · rw [e1, e2]
          exact lt_of_le_of_lt (min_le_left _ _) hlt
    have hBle := hA0min B hBF hBnd
    omega
  -- the span is at most 2
  have hd2 : (Q - P).val ≤ 2 := by
    by_contra h3
    push Not at h3
    have hm2 : 2 ≤ m := by have := ZMod.val_lt (Q - P); omega
    have hne1 : P ≠ P + 1 := by
      intro he
      have e : (1 : ZMod (m + 1)) = 0 := by linear_combination -he
      have e2 : (1 : ZMod (m + 1)).val = 1 := val_one' (by omega : 1 ≤ m)
      rw [e, ZMod.val_zero] at e2
      omega
    have hne2 : P ≠ P + 2 := by
      intro he
      have e : (2 : ZMod (m + 1)) = 0 := by linear_combination -he
      have e2 : (2 : ZMod (m + 1)).val = 2 := by
        have e2' : (2 : ZMod (m + 1)) = ((2 : ℕ) : ZMod (m + 1)) := by push_cast; ring
        rw [e2', val_natCast_of_lt (by omega : 2 < m + 1)]
      rw [e, ZMod.val_zero] at e2
      omega
    have hR1 : sbtw P (P + 1) Q := by
      rw [sbtw_val hne1]
      have e : P + 1 - P = 1 := by ring
      rw [e, val_one' (by omega : 1 ≤ m)]
      omega
    have hR2 : sbtw P (P + 2) Q := by
      rw [sbtw_val hne2]
      have e : P + 2 - P = ((2 : ℕ) : ZMod (m + 1)) := by
        rw [show ((2 : ℕ) : ZMod (m + 1)) = 2 from by push_cast; ring]; ring
      rw [e, val_natCast_of_lt (by omega : 2 < m + 1)]
      omega
    obtain ⟨B1, hB1F, hB1e⟩ := hcov (P + 1)
    obtain ⟨B2, hB2F, hB2e⟩ := hcov (P + 2)
    by_cases hB1nd : B1.1 ≠ B1.2
    · exact hmin B1 hB1F hB1nd (P + 1) (by
        rcases hB1e with h | h
        · exact Or.inl h
        · exact Or.inr h) hR1
    · by_cases hB2nd : B2.1 ≠ B2.2
      · exact hmin B2 hB2F hB2nd (P + 2) (by
          rcases hB2e with h | h
          · exact Or.inl h
          · exact Or.inr h) hR2
      · push Not at hB1nd hB2nd
        have e := hdeg B1 hB1F B2 hB2F hB1nd hB2nd
        have g1 : P + 1 = B1.1 := by
          rcases hB1e with h | h
          · exact h
          · rw [← hB1nd] at h; exact h
        have g2 : P + 2 = B2.1 := by
          rcases hB2e with h | h
          · exact h
          · rw [← hB2nd] at h; exact h
        have g3 : P + 1 = P + 2 := by rw [g1, g2, e]
        have e2 : (1 : ZMod (m + 1)) = 2 := by linear_combination g3
        have e3 : (1 : ZMod (m + 1)).val = 1 := val_one' (by omega : 1 ≤ m)
        have e4 : (2 : ZMod (m + 1)).val = 2 := by
          have e4' : (2 : ZMod (m + 1)) = ((2 : ℕ) : ZMod (m + 1)) := by push_cast; ring
          rw [e4', val_natCast_of_lt (by omega : 2 < m + 1)]
        rw [e2, e4] at e3
        omega
  rcases eq_or_ne (Q - P).val 1 with hd1 | hd1
  · exact Or.inl hd1
  · right
    have hd2' : (Q - P).val = 2 := by omega
    refine ⟨hd2', ?_⟩
    have hm2 : 2 ≤ m := by have := ZMod.val_lt (Q - P); omega
    have hne1 : P ≠ P + 1 := by
      intro he
      have e : (1 : ZMod (m + 1)) = 0 := by linear_combination -he
      have e2 : (1 : ZMod (m + 1)).val = 1 := val_one' (by omega : 1 ≤ m)
      rw [e, ZMod.val_zero] at e2
      omega
    have hR1 : sbtw P (P + 1) Q := by
      rw [sbtw_val hne1]
      have e : P + 1 - P = 1 := by ring
      rw [e, val_one' (by omega : 1 ≤ m), hd2']
      omega
    obtain ⟨B1, hB1F, hB1e⟩ := hcov (P + 1)
    by_cases hB1nd : B1.1 ≠ B1.2
    · exact (hmin B1 hB1F hB1nd (P + 1) (by
        rcases hB1e with h | h
        · exact Or.inl h
        · exact Or.inr h) hR1).elim
    · push Not at hB1nd
      have g1 : B1.1 = P + 1 := by
        rcases hB1e with h | h
        · exact h.symm
        · rw [← hB1nd] at h; exact h.symm
      have g2 : B1 = (P + 1, P + 1) := Prod.ext g1 (hB1nd.symm.trans g1)
      rw [g2] at hB1F
      exact hB1F

/-- The minimal-span non-degenerate chord gives either a boundary edge or a
span-2 chord around the degenerate point. -/
theorem boundary_data {m : ℕ} {F : Finset (Chord (m + 1))}
    (hnc : ChordNonCrossing F) (hdj : ChordDisjoint F)
    (hcov : ∀ p : ZMod (m + 1), ∃ A ∈ F, p = A.1 ∨ p = A.2)
    (hdeg : ∀ A ∈ F, ∀ B ∈ F, A.1 = A.2 → B.1 = B.2 → A = B)
    (hF2 : 2 ≤ F.card) :
    (∃ U V : ZMod (m + 1), (V - U).val = 1 ∧
      ∃ B ∈ F, (B.1 = V ∧ B.2 = U) ∨ (B.1 = U ∧ B.2 = V)) ∨
    (∃ U V R : ZMod (m + 1), (V - U).val = 2 ∧ (R - U).val = 1 ∧ (R, R) ∈ F ∧
      ∃ B ∈ F, (B.1 = V ∧ B.2 = U) ∨ (B.1 = U ∧ B.2 = V)) := by
  obtain ⟨A1, hA1, B1, hB1, hAB1⟩ := Finset.one_lt_card.1 hF2
  have hS : (F.filter fun A => A.1 ≠ A.2).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have hall : ∀ A ∈ F, A.1 = A.2 := by
      intro A hA
      have h2 := Finset.filter_eq_empty_iff.1 h hA
      exact of_not_not h2
    exact hAB1 (hdeg A1 hA1 B1 hB1 (hall A1 hA1) (hall B1 hB1))
  obtain ⟨A0, hA0, hA0min⟩ := Finset.exists_min_image _
    (fun A => min (A.2 - A.1).val (A.1 - A.2).val) hS
  rw [Finset.mem_filter] at hA0
  obtain ⟨hA0F, hA0ne⟩ := hA0
  have hA0min' : ∀ B ∈ F, B.1 ≠ B.2 → min (A0.2 - A0.1).val (A0.1 - A0.2).val ≤
      min (B.2 - B.1).val (B.1 - B.2).val := by
    intro B hBF hBne
    exact hA0min B (Finset.mem_filter.2 ⟨hBF, hBne⟩)
  have hd0 : 1 ≤ min (A0.2 - A0.1).val (A0.1 - A0.2).val := by
    have h1 : (A0.2 - A0.1).val ≠ 0 := fun hz => hA0ne (by
      have e := ZMod.natCast_zmod_val (A0.2 - A0.1)
      rw [hz, Nat.cast_zero] at e
      have e' : A0.2 - A0.1 = 0 := e.symm
      rw [sub_eq_zero] at e'
      exact e'.symm)
    have h2 : (A0.1 - A0.2).val ≠ 0 := fun hz => hA0ne (by
      have e := ZMod.natCast_zmod_val (A0.1 - A0.2)
      rw [hz, Nat.cast_zero] at e
      have e' : A0.1 - A0.2 = 0 := e.symm
      rw [sub_eq_zero] at e'
      exact e')
    omega
  by_cases hle : (A0.2 - A0.1).val ≤ (A0.1 - A0.2).val
  · -- orient `P = A0.1`, `Q = A0.2`
    have hdPQ : (A0.2 - A0.1).val = min (A0.2 - A0.1).val (A0.1 - A0.2).val :=
      (min_eq_left hle).symm
    have hPQ : A0 = (A0.1, A0.2) ∨ A0 = (A0.2, A0.1) := Or.inl (Prod.eta A0).symm
    rcases boundary_analysis hnc hdj hcov hdeg hA0F hA0ne hA0min' hPQ hdPQ hd0 with hd1 | ⟨hd2, hR⟩
    · exact Or.inl ⟨A0.1, A0.2, hd1, A0, hA0F, Or.inr ⟨rfl, rfl⟩⟩
    · exact Or.inr ⟨A0.1, A0.2, A0.1 + 1, hd2, by
        have e : A0.1 + 1 - A0.1 = 1 := by ring
        rw [e, val_one' (by have := ZMod.val_lt (A0.2 - A0.1); omega)], hR, A0, hA0F, Or.inr ⟨rfl, rfl⟩⟩
  · -- orient `P = A0.2`, `Q = A0.1`
    have hdPQ : (A0.1 - A0.2).val = min (A0.2 - A0.1).val (A0.1 - A0.2).val :=
      (min_eq_right (by omega : (A0.1 - A0.2).val ≤ (A0.2 - A0.1).val)).symm
    have hPQ : A0 = (A0.2, A0.1) ∨ A0 = (A0.1, A0.2) := Or.inr (Prod.eta A0).symm
    rcases boundary_analysis hnc hdj hcov hdeg hA0F hA0ne hA0min' hPQ hdPQ hd0 with hd1 | ⟨hd2, hR⟩
    · exact Or.inl ⟨A0.2, A0.1, hd1, A0, hA0F, Or.inl ⟨rfl, rfl⟩⟩
    · exact Or.inr ⟨A0.2, A0.1, A0.2 + 1, hd2, by
        have e : A0.2 + 1 - A0.2 = 1 := by ring
        rw [e, val_one' (by have := ZMod.val_lt (A0.1 - A0.2); omega)], hR, A0, hA0F, Or.inl ⟨rfl, rfl⟩⟩

theorem const_sum_of_aligned {m : ℕ} (F : Finset (Chord (m + 1)))
    (hnc : ChordNonCrossing F) (hdj : ChordDisjoint F) (hal : ChordAligned F)
    (hcov : ∀ p : ZMod (m + 1), ∃ A ∈ F, p = A.1 ∨ p = A.2)
    (hdeg : ∀ A ∈ F, ∀ B ∈ F, A.1 = A.2 → B.1 = B.2 → A = B) :
    ∃ c₀ : ZMod (m + 1), ∀ A ∈ F, A.1 + A.2 = c₀ := by
  rcases F.eq_empty_or_nonempty with hF | hF
  · -- `F` empty is impossible: the circle is nonempty but must be covered
    exfalso
    obtain ⟨A, hA, -⟩ := hcov 0
    rw [hF] at hA
    simp at hA
  · by_cases hF1 : F.card = 1
    · -- a single chord: take `c₀` to be its sum
      obtain ⟨A, hA⟩ := Finset.card_eq_one.1 hF1
      refine ⟨A.1 + A.2, ?_⟩
      intro B hB
      rw [hA] at hB
      rw [Finset.mem_singleton.1 hB]
    · -- `|F| ≥ 2`: the boundary analysis, then peeling
      have hF2 : 2 ≤ F.card := by
        have h0 : F.card ≠ 0 := by
          intro hz
          rw [Finset.card_eq_zero.1 hz] at hF
          exact Finset.not_nonempty_empty hF
        omega
      rcases boundary_data hnc hdj hcov hdeg hF2 with ⟨U, V, hUV, hc0⟩ |
        ⟨U, V, R, hUV, hRU, hRR, hc0⟩
      · -- boundary edge `{U, V}` with `V = U + 1`: peel with dummy `R = V`
        refine ⟨U + V, peel hnc hdj hal hcov hdeg (by omega : 1 ≤ (V - U).val)
          (by omega : (V - U).val ≤ 2) (by omega : (V - U).val ≤ (V - U).val) hc0 ?_ (Or.inr rfl) ?_⟩
        · intro p hp
          exfalso
          have hpU : p = U := by
            by_contra hUp
            rw [sbtw_val (Ne.symm hUp), hUV] at hp
            have h1 : (p - U).val = 0 := by omega
            apply hUp
            have e : p - U = 0 := by
              have e2 := ZMod.natCast_zmod_val (p - U)
              rw [h1, Nat.cast_zero] at e2
              exact e2.symm
            rw [sub_eq_zero] at e
            exact e
          rw [hpU, sbtw_zmod_def] at hp
          omega
        · intro hVV
          exfalso
          obtain ⟨B, hBF, hBe⟩ := hc0
          have hne : (V, V) ≠ B := by
            intro he
            rcases hBe with ⟨e1, e2⟩ | ⟨e1, e2⟩
            · have h2 : (V, V).2 = B.2 := by rw [he]
              rw [e2] at h2
              have h2' : V = U := h2
              rw [show V - U = 0 from by rw [h2', sub_self], ZMod.val_zero] at hUV
              omega
            · have h2 : (V, V).1 = B.1 := by rw [he]
              rw [e1] at h2
              have h2' : V = U := h2
              rw [show V - U = 0 from by rw [h2', sub_self], ZMod.val_zero] at hUV
              omega
          have hd := hdj (V, V) hVV B hBF hne
          rcases hBe with ⟨e1, e2⟩ | ⟨e1, e2⟩
          · rw [e1] at hd
            exact hd.1 rfl
          · rw [e2] at hd
            exact hd.2.1 rfl
      · -- span-2 chord `{U, V}` around the degenerate point `R = U + 1`
        have hVR : V ≠ R := by
          intro he
          rw [he, hRU] at hUV
          omega
        have hUR : U ≠ R := by
          intro he
          rw [← he, sub_self, ZMod.val_zero] at hRU
          omega
        refine ⟨U + V, peel hnc hdj hal hcov hdeg (by omega : 1 ≤ (V - U).val)
          (by omega : (V - U).val ≤ 2) (by omega : (R - U).val ≤ (V - U).val) hc0 ?_ (Or.inl hRR)
          (fun _ => ⟨hVR, hUR⟩)⟩
        · intro p hp
          have hUp : U ≠ p := by
            intro he
            rw [← he, sbtw_zmod_def] at hp
            omega
          rw [sbtw_val hUp, hUV] at hp
          have hp1 : (p - U).val = 1 := by
            have h0 : (p - U).val ≠ 0 := by
              intro hz
              apply hUp
              have e : p - U = 0 := by
                have e2 := ZMod.natCast_zmod_val (p - U)
                rw [hz, Nat.cast_zero] at e2
                exact e2.symm
              rw [sub_eq_zero] at e
              exact e.symm
            omega
          have e : p - U = 1 := ZMod.val_injective _ (by
            rw [hp1, val_one' (by have := ZMod.val_lt (V - U); omega)])
          have eR : R - U = 1 := ZMod.val_injective _ (by
            rw [hRU, val_one' (by have := ZMod.val_lt (V - U); omega)])
          exact sub_left_injective (show p - U = R - U from by rw [e, eR])


/-- Chords with constant endpoint-sum do not cross: for `P, Q, K` on the circle, the
chords `{P, K - P}` and `{Q, K - Q}` have `Q` and `K - Q` on the same side of
`{P, K - P}`. This is the algebraic form of "parallel chords of a regular polygon
are exactly the pairs with constant sum". -/
theorem sbtw_sum_const {n : ℕ} {P Q K : ZMod (n + 1)} (hPQ : P ≠ Q) (hKP : K - Q ≠ P) :
    sbtw P Q (K - P) ↔ sbtw P (K - Q) (K - P) := by
  have e1 : K - P - P = K - 2 * P := by ring
  have e2 : (K - Q) - P = (K - 2 * P) - (Q - P) := by ring
  rw [sbtw_val hPQ, sbtw_val hKP.symm, e1, e2]
  rw [val_sub_if (Q - P) (K - 2 * P)]
  have hp0 : (Q - P).val ≠ 0 := by
    intro he
    apply hPQ
    have h : Q - P = 0 := by
      rw [← ZMod.natCast_zmod_val (Q - P), he, Nat.cast_zero]
    exact (sub_eq_zero.mp h).symm
  have hpq : (Q - P).val ≠ (K - 2 * P).val := by
    intro he
    apply hKP
    have h : Q - P = K - 2 * P := ZMod.val_injective (n + 1) he
    have h2 : K - Q - P = 0 := by linear_combination -h
    exact sub_eq_zero.mp h2
  have hp := ZMod.val_lt (Q - P); have hq := ZMod.val_lt (K - 2 * P)
  by_cases hcase : (Q - P).val ≤ (K - 2 * P).val
  · rw [if_pos hcase]
    omega
  · rw [if_neg hcase]
    omega

/-- The arithmetic progression labelling with step `s` (a unit). -/
def APEquiv {n : ℕ} (s : (ZMod (n + 1))ˣ) : ZMod (n + 1) ≃ ZMod (n + 1) where
  toFun x := (s : ZMod (n + 1)) * x
  invFun y := ((s⁻¹ : (ZMod (n + 1))ˣ) : ZMod (n + 1)) * y
  left_inv x := by
    show ((s⁻¹ : (ZMod (n + 1))ˣ) : ZMod (n + 1)) * ((s : ZMod (n + 1)) * x) = x
    rw [← mul_assoc, Units.inv_mul, one_mul]
  right_inv y := by
    show (s : ZMod (n + 1)) * (((s⁻¹ : (ZMod (n + 1))ˣ) : ZMod (n + 1)) * y) = y
    rw [← mul_assoc, Units.mul_inv, one_mul]

theorem APEquiv_apply {n : ℕ} (s : (ZMod (n + 1))ˣ) (x : ZMod (n + 1)) :
    APEquiv s x = (s : ZMod (n + 1)) * x := rfl

theorem APEquiv_zero {n : ℕ} (s : (ZMod (n + 1))ˣ) : APEquiv s 0 = 0 := mul_zero _

theorem APEquiv_linear {n : ℕ} (s : (ZMod (n + 1))ˣ) : Linear (APEquiv s) :=
  ⟨s, fun _ => rfl⟩

/-- Arithmetic progressions are beautiful: chords with a given label-sum have constant
endpoint-sum, hence are parallel. -/
theorem APEquiv_beautiful {n : ℕ} (s : (ZMod (n + 1))ˣ) : Beautiful (APEquiv s) := by
  intro a b c d hab hbc hcd hsum hc
  have hsumz : (a : ZMod (n + 1)) + d = b + c := by
    have h1 : ((a.val + d.val : ℕ) : ZMod (n + 1)) = ((b.val + c.val : ℕ) : ZMod (n + 1)) := by
      rw [hsum]
    rw [Nat.cast_add, Nat.cast_add, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val,
      ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at h1
    exact h1
  have uinj : Function.Injective fun x => (s : ZMod (n + 1)) * x := by
    intro x y h
    have h2 : (↑s : ZMod (n + 1)) * x = (↑s : ZMod (n + 1)) * y := h
    have h3 := congrArg (((s⁻¹ : (ZMod (n + 1))ˣ) : ZMod (n + 1)) * ·) h2
    rwa [← mul_assoc, ← mul_assoc, Units.inv_mul, one_mul, one_mul] at h3
  have hd1 : (s : ZMod (n + 1)) * a ≠ s * b := by
    intro h
    have h2 : a = b := uinj h
    rw [h2] at hab
    exact absurd hab (lt_irrefl _)
  have hd2 : (s : ZMod (n + 1)) * a + s * d - s * b ≠ s * a := by
    intro h
    have h2 : (s : ZMod (n + 1)) * d = s * b := by linear_combination h
    have h3 : d = b := uinj h2
    rw [h3] at hcd
    omega
  have key := sbtw_sum_const (P := (s : ZMod (n + 1)) * a) (Q := (s : ZMod (n + 1)) * b)
    (K := (s : ZMod (n + 1)) * a + s * d) hd1 hd2
  have e1 : (s : ZMod (n + 1)) * a + s * d - s * a = s * d := by ring
  have e2 : (s : ZMod (n + 1)) * a + s * d - s * b = s * c := by
    have h3 : (s : ZMod (n + 1)) * a + s * d - s * b = s * (a + d - b) := by ring
    rw [h3]
    have h4 : a + d - b = c := by rw [hsumz]; ring
    rw [h4]
  rw [e1, e2] at key
  unfold Crossing at hc
  exact hc (propext key)

/-- The number of linear beautiful normalized labellings of `[0, n]` is `φ (n + 1)`. -/
theorem linear_count {n : ℕ} (_hn : 2 ≤ n) :
    ((Finset.univ.filter fun τ : ZMod (n + 1) ≃ ZMod (n + 1) =>
      (Beautiful τ ∧ τ 0 = 0) ∧ Linear τ).card) = (n + 1).totient := by
  rw [← ZMod.card_units_eq_totient (n + 1), ← Finset.card_univ]
  symm
  apply Finset.card_bij (fun s _ => APEquiv s)
  · intro s _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨⟨APEquiv_beautiful s, APEquiv_zero s⟩,
      APEquiv_linear s⟩⟩
  · intro s _ t _ h
    have h1 : APEquiv s 1 = APEquiv t 1 := by rw [h]
    rw [APEquiv_apply, APEquiv_apply, mul_one, mul_one] at h1
    exact Units.ext h1
  · intro τ hτ
    obtain ⟨s, hs⟩ := (Finset.mem_filter.mp hτ).2.2
    exact ⟨s, Finset.mem_univ s, Equiv.ext fun x => (hs x).symm⟩


/-! ## N-generic circle machinery (for the aligned-chords claim) -/

def circleInclN {N : ℕ} [NeZero N] [NeZero (N - 1)] (q : ZMod N) (x : ZMod (N - 1)) : ZMod N :=
  q + 1 + x.val

theorem circleInclN_ne_q {N : ℕ} [NeZero N] [NeZero (N - 1)] (q : ZMod N) (x : ZMod (N - 1)) :
    circleInclN q x ≠ q := by
  intro h
  unfold circleInclN at h
  have h1 : (1 : ZMod N) + x.val = 0 := by
    have h2 : q + ((1 : ZMod N) + x.val) = q + 0 := by
      rw [show q + ((1 : ZMod N) + x.val) = q + 1 + x.val from by ring, h, add_zero]
    exact add_left_cancel h2
  have h2 : (x.val : ZMod N) = -1 := by linear_combination h1
  have h3 : (x.val : ZMod N).val = x.val :=
    ZMod.val_cast_of_lt (by have := ZMod.val_lt x; omega)
  have h4 : ((-1 : ZMod N)).val = N - 1 := by
    have h5 : ((-1 : ZMod N)) = ((N - 1 : ℕ) : ZMod N) := by
      rw [neg_eq_iff_add_eq_zero, ← Nat.cast_one, ← Nat.cast_add]
      have : 1 + (N - 1) = N := by have := NeZero.one_le (n := N); omega
      rw [this, ZMod.natCast_self]
    rw [h5, ZMod.val_cast_of_lt (by have := NeZero.one_le (n := N); omega : N - 1 < N)]
  rw [h2, h4] at h3
  have := ZMod.val_lt x
  omega

theorem circleInclN_injective {N : ℕ} [NeZero N] [NeZero (N - 1)] (q : ZMod N) :
    Function.Injective (circleInclN q) := by
  intro x y h
  unfold circleInclN at h
  have h1 : (x.val : ZMod N) = y.val := by
    have := add_left_cancel_iff (a := q + 1) (b := (x.val : ZMod N))
      (c := (y.val : ZMod N))
    exact add_left_cancel_iff.mp h
  have h2 : (x.val : ZMod N).val = x.val :=
    ZMod.val_cast_of_lt (by have := ZMod.val_lt x; omega)
  have h3 : (y.val : ZMod N).val = y.val :=
    ZMod.val_cast_of_lt (by have := ZMod.val_lt y; omega)
  have h4 : x.val = y.val := by rw [← h2, h1, h3]
  exact ZMod.val_injective _ h4

/-- The strict betweenness preservation of `circleInclN`: the main computation. -/
theorem circleInclN_sbtw {N : ℕ} [NeZero N] [NeZero (N - 1)] {q : ZMod N} {x y z : ZMod (N - 1)} (hxy : x ≠ y) :
    sbtw (circleInclN q x) (circleInclN q y) (circleInclN q z) ↔ sbtw x y z := by
  have hxy' : circleInclN q x ≠ circleInclN q y :=
    fun h => hxy (circleInclN_injective q h)
  have hxv : ((x.val : ZMod N)).val = x.val :=
    ZMod.val_cast_of_lt (by have := ZMod.val_lt x; omega)
  have hyv : ((y.val : ZMod N)).val = y.val :=
    ZMod.val_cast_of_lt (by have := ZMod.val_lt y; omega)
  have zv : ((z.val : ZMod N)).val = z.val :=
    ZMod.val_cast_of_lt (by have := ZMod.val_lt z; omega)
  have e2 : circleInclN q y - circleInclN q x = (y.val : ZMod N) - x.val := by
    unfold circleInclN
    ring
  have e3 : circleInclN q z - circleInclN q x = (z.val : ZMod N) - x.val := by
    unfold circleInclN
    ring
  have hxyv : (x.val : ZMod N) ≠ (y.val : ZMod N) := by
    intro h
    apply hxy
    apply ZMod.val_injective (N - 1)
    rw [← hxv, ← hyv, h]
  rw [sbtw_val hxy', e2, e3, val_sub' (y.val : ZMod N) (x.val : ZMod N),
    val_sub' (z.val : ZMod N) (x.val : ZMod N), hxv, hyv, zv]
  rw [sbtw_val hxy, val_sub' y x, val_sub' z x]
  have hx := ZMod.val_lt x; have hy := ZMod.val_lt y; have hz := ZMod.val_lt z
  by_cases h1 : x.val ≤ y.val
  · have m1 : (y.val + (N) - x.val) % (N) = y.val - x.val := by
      have e' : y.val + (N) - x.val = (y.val - x.val) + (N) := by omega
      rw [e', Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : y.val - x.val < N)]
    have m1' : (y.val + (N - 1) - x.val) % (N - 1) = y.val - x.val := by
      have e' : y.val + (N - 1) - x.val = (y.val - x.val) + (N - 1) := by omega
      rw [e', Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : y.val - x.val < N - 1)]
    rw [m1, m1']
    by_cases h2 : x.val ≤ z.val
    · have m2 : (z.val + (N) - x.val) % (N) = z.val - x.val := by
        have e' : z.val + (N) - x.val = (z.val - x.val) + (N) := by omega
        rw [e', Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : z.val - x.val < N)]
      have m2' : (z.val + (N - 1) - x.val) % (N - 1) = z.val - x.val := by
        have e' : z.val + (N - 1) - x.val = (z.val - x.val) + (N - 1) := by omega
        rw [e', Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : z.val - x.val < N - 1)]
      rw [m2, m2']
    · have m2 : (z.val + (N) - x.val) % (N) = z.val + (N) - x.val :=
        Nat.mod_eq_of_lt (by omega : z.val + (N) - x.val < N)
      have m2' : (z.val + (N - 1) - x.val) % (N - 1) = z.val + (N - 1) - x.val :=
        Nat.mod_eq_of_lt (by omega : z.val + (N - 1) - x.val < N - 1)
      rw [m2, m2']
      omega
  · have m1 : (y.val + (N) - x.val) % (N) = y.val + (N) - x.val :=
      Nat.mod_eq_of_lt (by omega : y.val + (N) - x.val < N)
    have m1' : (y.val + (N - 1) - x.val) % (N - 1) = y.val + (N - 1) - x.val :=
      Nat.mod_eq_of_lt (by omega : y.val + (N - 1) - x.val < N - 1)
    rw [m1, m1']
    by_cases h2 : x.val ≤ z.val
    · have m2 : (z.val + (N) - x.val) % (N) = z.val - x.val := by
        have e' : z.val + (N) - x.val = (z.val - x.val) + (N) := by omega
        rw [e', Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : z.val - x.val < N)]
      have m2' : (z.val + (N - 1) - x.val) % (N - 1) = z.val - x.val := by
        have e' : z.val + (N - 1) - x.val = (z.val - x.val) + (N - 1) := by omega
        rw [e', Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : z.val - x.val < N - 1)]
      rw [m2, m2']
      omega
    · have m2 : (z.val + (N) - x.val) % (N) = z.val + (N) - x.val :=
        Nat.mod_eq_of_lt (by omega : z.val + (N) - x.val < N)
      have m2' : (z.val + (N - 1) - x.val) % (N - 1) = z.val + (N - 1) - x.val :=
        Nat.mod_eq_of_lt (by omega : z.val + (N - 1) - x.val < N - 1)
      rw [m2, m2']
      omega

/-- The circle `ZMod (N - 1)` identified with the circle `ZMod N` punctured at
`q`, preserving the circular order. -/
def circleIsoN {N : ℕ} [NeZero N] [NeZero (N - 1)] (q : ZMod N) : ZMod (N - 1) ≃ {z : ZMod N // z ≠ q} where
  toFun x := ⟨circleInclN q x, circleInclN_ne_q q x⟩
  invFun y := (((y.1 - q - 1).val : ℕ) : ZMod (N - 1))
  left_inv x := by
    have e : circleInclN q x - q - 1 = (x.val : ZMod N) := by unfold circleInclN; ring
    show (((circleInclN q x - q - 1).val : ℕ) : ZMod (N - 1)) = x
    rw [e, ZMod.val_natCast, Nat.mod_eq_of_lt (by have := ZMod.val_lt x; omega : x.val < N),
      ZMod.natCast_zmod_val]
  right_inv y := by
    apply Subtype.ext
    have hne : (y.1 - q - 1).val ≠ N - 1 := by
      intro he
      apply y.2
      have h1 : (y.1 - q - 1 : ZMod N) = -1 := by
        apply ZMod.val_injective (N)
        rw [he]
        have h4 : ((-1 : ZMod N)).val = N - 1 := by
          have h5 : ((-1 : ZMod N)) = ((N - 1 : ℕ) : ZMod N) := by
            rw [neg_eq_iff_add_eq_zero, ← Nat.cast_one, ← Nat.cast_add]
            have : 1 + (N - 1) = N := by have := NeZero.one_le (n := N); omega
            rw [this, ZMod.natCast_self]
          rw [h5, ZMod.val_cast_of_lt (by have := NeZero.one_le (n := N); omega : N - 1 < N)]
        rw [h4]
      have h2 : y.1 = q := by linear_combination h1
      exact h2
    have hlt : (y.1 - q - 1).val < N - 1 := by
      have := ZMod.val_lt (y.1 - q - 1)
      omega
    show circleInclN q (((y.1 - q - 1).val : ℕ) : ZMod (N - 1)) = y.1
    unfold circleInclN
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hlt, ZMod.natCast_zmod_val]
    ring

/-- The map from the punctured circle back to `ZMod (N - 1)`. -/
def cutCircleN {N : ℕ} [NeZero N] [NeZero (N - 1)] (q : ZMod N) (y : {z : ZMod N // z ≠ q}) : ZMod (N - 1) :=
  (circleIsoN q).symm y

theorem circleInclN_cutCircleN {N : ℕ} [NeZero N] [NeZero (N - 1)] (q : ZMod N) (y : {z : ZMod N // z ≠ q}) :
    circleInclN q (cutCircleN q y) = y.1 := by
  have h := (circleIsoN q).right_inv y
  exact Subtype.ext_iff.mp h

/-- Strict betweenness preservation of `cutCircleN`. -/
theorem cutCircleN_sbtw {N : ℕ} [NeZero N] [NeZero (N - 1)] {q : ZMod N} (a b c : {z : ZMod N // z ≠ q})
    (hab : a.1 ≠ b.1) :
    sbtw (cutCircleN q a) (cutCircleN q b) (cutCircleN q c) ↔ sbtw a.1 b.1 c.1 := by
  have hab' : cutCircleN q a ≠ cutCircleN q b := by
    intro h
    apply hab
    rw [← circleInclN_cutCircleN q a, ← circleInclN_cutCircleN q b, h]
  rw [← circleInclN_sbtw (q := q) (x := cutCircleN q a) (y := cutCircleN q b)
    (z := cutCircleN q c) hab']
  rw [circleInclN_cutCircleN, circleInclN_cutCircleN, circleInclN_cutCircleN]

/-- Deletion of the top label transports a non-aligned triple of `k`-chords to a
smaller arrangement. -/
theorem ChordSep.circleInclN {N : ℕ} [NeZero N] [NeZero (N - 1)] {q : ZMod N}
    {A B C : Chord (N - 1)}
    (h1 : A.1 ≠ B.1) (h2 : A.1 ≠ B.2) (h3 : A.1 ≠ C.1) (h4 : A.1 ≠ C.2) :
    ChordSep (circleInclN q A.1, circleInclN q A.2) (circleInclN q B.1, circleInclN q B.2)
      (circleInclN q C.1, circleInclN q C.2) ↔ ChordSep A B C := by
  unfold ChordSep
  rw [circleInclN_sbtw h1, circleInclN_sbtw h2, circleInclN_sbtw h3, circleInclN_sbtw h4]

/-- Inclusion of labels `[0, n]` into `[0, N - 1]`. -/
def labelInclN {N : ℕ} [NeZero N] [NeZero (N - 1)] (x : ZMod (N - 1)) : ZMod N :=
  ((x.val : ℕ) : ZMod N)

theorem labelInclN_val {N : ℕ} [NeZero N] [NeZero (N - 1)] (x : ZMod (N - 1)) : (labelInclN x).val = x.val :=
  ZMod.val_cast_of_lt (by have := ZMod.val_lt x; omega)

/-- The largest label `N - 1` as an element of `ZMod N`. -/
def topLabelN {N : ℕ} [NeZero N] [NeZero (N - 1)] : ZMod N :=
  ((N - 1 : ℕ) : ZMod N)

theorem topLabelN_val {N : ℕ} [NeZero N] [NeZero (N - 1)] : (topLabelN : ZMod N).val = N - 1 :=
  ZMod.val_cast_of_lt (by have := NeZero.one_le (n := N); omega : N - 1 < N)

theorem labelInclN_ne_top {N : ℕ} [NeZero N] [NeZero (N - 1)] (x : ZMod (N - 1)) : labelInclN x ≠ topLabelN := by
  intro h
  have h1 : (labelInclN x : ZMod N).val = (topLabelN : ZMod N).val := by rw [h]
  rw [labelInclN_val, topLabelN_val] at h1
  have := ZMod.val_lt x
  omega

theorem val_lt_of_ne_topN {N : ℕ} [NeZero N] [NeZero (N - 1)] {x : ZMod N} (h : x ≠ topLabelN) : x.val < N - 1 := by
  have h1 : x.val ≠ N - 1 := by
    intro he
    apply h
    rw [← ZMod.natCast_zmod_val x, he]
    rfl
  have := ZMod.val_lt x
  omega

/-- The equivalence between labels `[0, n]` and non-top labels of `[0, N - 1]`. -/
def labelInclEquivN {N : ℕ} [NeZero N] [NeZero (N - 1)] : ZMod (N - 1) ≃ {z : ZMod N // z ≠ topLabelN} where
  toFun x := ⟨labelInclN x, labelInclN_ne_top x⟩
  invFun y := ((y.1.val : ℕ) : ZMod (N - 1))
  left_inv x := by
    show (((⟨labelInclN x, labelInclN_ne_top x⟩ : {z : ZMod N // z ≠ topLabelN}).1.val : ℕ) :
        ZMod (N - 1)) = x
    rw [labelInclN_val, ZMod.natCast_zmod_val]
  right_inv y := by
    apply Subtype.ext
    show labelInclN ((y.1.val : ℕ) : ZMod (N - 1)) = y.1
    unfold labelInclN
    have hy : y.1.val < N - 1 := val_lt_of_ne_topN y.2
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hy, ZMod.natCast_zmod_val]

/-- Deletion of the largest label from a labelling of `[0, N - 1]`, producing a
labelling of `[0, n]`: positions are re-indexed by cutting the circle at the deleted
point. -/
def DelN {N : ℕ} [NeZero N] [NeZero (N - 1)] (S : ZMod N ≃ ZMod N) : ZMod (N - 1) ≃ ZMod (N - 1) :=
  labelInclEquivN.trans
    ((Equiv.subtypeEquiv S fun _ => not_congr (Equiv.apply_eq_iff_eq S).symm).trans
      (circleIsoN (S topLabelN)).symm)

theorem DelN_apply {N : ℕ} [NeZero N] [NeZero (N - 1)] (S : ZMod N ≃ ZMod N) (x : ZMod (N - 1)) :
    DelN S x = cutCircleN (S topLabelN) ⟨S (labelInclN x), by
      rw [S.injective.ne_iff]
      exact labelInclN_ne_top x⟩ :=
  rfl

/-- Deletion preserves beauty. -/
theorem DelN_beautiful {N : ℕ} [NeZero N] [NeZero (N - 1)] {S : ZMod N ≃ ZMod N} (h : Beautiful S) :
    Beautiful (DelN S) := by
  intro a b c d hab hbc hcd hsum hcDel
  have hv : ∀ x : ZMod (N - 1), (labelInclN x : ZMod N).val = x.val := labelInclN_val
  apply h (labelInclN a) (labelInclN b) (labelInclN c) (labelInclN d)
    (by rw [hv, hv]; exact hab) (by rw [hv, hv]; exact hbc) (by rw [hv, hv]; exact hcd)
    (by rw [hv, hv, hv, hv]; exact hsum)
  rw [DelN_apply, DelN_apply, DelN_apply, DelN_apply] at hcDel
  unfold Crossing at hcDel ⊢
  have inj : ∀ x y : ZMod (N - 1), x.val < y.val → S (labelInclN x) ≠ S (labelInclN y) := by
    intro x y hxy he
    have h1 : labelInclN x = labelInclN y := S.injective he
    have h2 : x.val = y.val := by rw [← labelInclN_val x, h1, labelInclN_val]
    omega
  rw [cutCircleN_sbtw _ _ _ (inj a b hab), cutCircleN_sbtw _ _ _ (inj a c (hab.trans hbc))]
    at hcDel
  exact hcDel

/-- Inclusion of labels `[1, N - 1]` (identified with `[0, N - 2]` shifted by one)
into `[0, N - 1]`. -/
def succLabelEquivN {N : ℕ} [NeZero N] [NeZero (N - 1)] : ZMod (N - 1) ≃ {z : ZMod N // z ≠ 0} where
  toFun x := ⟨((x.val + 1 : ℕ) : ZMod N), by
    intro h
    have h1 : (((x.val + 1 : ℕ) : ZMod N)).val = (0 : ZMod N).val := by rw [h]
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by have := ZMod.val_lt x; omega : x.val + 1 < N),
      ZMod.val_zero] at h1
    omega⟩
  invFun y := ((y.1.val - 1 : ℕ) : ZMod (N - 1))
  left_inv x := by
    show ((((x.val + 1 : ℕ) : ZMod N)).val - 1 : ℕ) = x
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by have := ZMod.val_lt x; omega : x.val + 1 < N)]
    have := ZMod.val_lt x
    rw [show x.val + 1 - 1 = x.val from by omega, ZMod.natCast_zmod_val]
  right_inv y := by
    apply Subtype.ext
    show (((y.1.val - 1 : ℕ) : ZMod (N - 1)).val + 1 : ℕ) = y.1
    have hy : 1 ≤ y.1.val := by
      have h1 : y.1.val ≠ 0 := by
        intro he
        apply y.2
        apply ZMod.val_injective (N)
        rw [he, ZMod.val_zero]
      have := ZMod.val_lt y.1
      omega
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by have := ZMod.val_lt y.1; omega :
      y.1.val - 1 < N - 1)]
    rw [show y.1.val - 1 + 1 = y.1.val from by omega, ZMod.natCast_zmod_val]

/-- Deletion of the label `0` from an arrangement of `[0, N - 1]`, with all other
labels decreased by `1`, producing an arrangement of `[0, n]`. -/
def DelZeroN {N : ℕ} [NeZero N] [NeZero (N - 1)] (σ : ZMod N ≃ ZMod N) : ZMod (N - 1) ≃ ZMod (N - 1) :=
  succLabelEquivN.trans
    ((Equiv.subtypeEquiv σ fun _ => not_congr (Equiv.apply_eq_iff_eq σ).symm).trans
      (circleIsoN (σ 0)).symm)

theorem DelZeroN_apply {N : ℕ} [NeZero N] [NeZero (N - 1)] (σ : ZMod N ≃ ZMod N) (x : ZMod (N - 1)) :
    DelZeroN σ x = cutCircleN (σ 0) ⟨σ ((x.val + 1 : ℕ) : ZMod N),
      mt (Equiv.apply_eq_iff_eq σ).mp (by
        intro h
        have h1 : (((x.val + 1 : ℕ) : ZMod N)).val = (0 : ZMod N).val := by rw [h]
        rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by have := ZMod.val_lt x; omega : x.val + 1 < N),
          ZMod.val_zero] at h1
        omega)⟩ := by
  apply ZMod.val_injective (N - 1)
  rfl

/-- `DelZeroN` preserves beauty. -/
theorem DelZeroN_beautiful {N : ℕ} [NeZero N] [NeZero (N - 1)] {σ : ZMod N ≃ ZMod N} (h : Beautiful σ) :
    Beautiful (DelZeroN σ) := by
  intro a b c d hab hbc hcd hsum hcDel
  have hv : ∀ x : ZMod (N - 1), (((x.val + 1 : ℕ) : ZMod N)).val = x.val + 1 := by
    intro x
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by have := ZMod.val_lt x; omega : x.val + 1 < N)]
  apply h (((a.val + 1 : ℕ) : ZMod N)) (((b.val + 1 : ℕ) : ZMod N))
    (((c.val + 1 : ℕ) : ZMod N)) (((d.val + 1 : ℕ) : ZMod N))
    (by rw [hv, hv]; omega) (by rw [hv, hv]; omega) (by rw [hv, hv]; omega)
    (by rw [hv, hv, hv, hv]; omega)
  rw [DelZeroN_apply, DelZeroN_apply, DelZeroN_apply, DelZeroN_apply] at hcDel
  unfold Crossing at hcDel ⊢
  have inj : ∀ x y : ZMod (N - 1), x.val < y.val →
      σ (((x.val + 1 : ℕ) : ZMod N)) ≠ σ (((y.val + 1 : ℕ) : ZMod N)) := by
    intro x y hxy he
    have h1 : ((x.val + 1 : ℕ) : ZMod N) = ((y.val + 1 : ℕ) : ZMod N) := σ.injective he
    have h2 : (((x.val + 1 : ℕ) : ZMod N)).val = (((y.val + 1 : ℕ) : ZMod N)).val := by
      rw [h1]
    rw [hv, hv] at h2
    omega
  rw [cutCircleN_sbtw _ _ _ (inj a b hab), cutCircleN_sbtw _ _ _ (inj a c (hab.trans hbc))] at hcDel
  exact hcDel

/-- Inclusion of labels `[1, n + 1]` (identified with `[0, n]` shifted by one) into
`[0, n + 1]`. -/
theorem aligned_step_del {N : ℕ} [NeZero N] [NeZero (N - 1)] {σ : ZMod N ≃ ZMod N}
    (hN : 4 ≤ N) (hσ : Beautiful σ)
    (ih : ∀ M < N, ∀ [NeZero M], ∀ σ' : ZMod M ≃ ZMod M, Beautiful σ' →
      ∀ k : ℕ, ChordAligned (kChords σ' k))
    {k : ℕ} {A B C : Chord N} (hA : A ∈ kChords σ k) (hB : B ∈ kChords σ k)
    (hC : C ∈ kChords σ k) (hAB : A ≠ B) (hBC : B ≠ C) (hAC : A ≠ C)
    (hdj : ChordDisjoint (kChords σ k))
    (hnotop : A.2 ≠ σ topLabelN ∧ B.2 ≠ σ topLabelN ∧ C.2 ≠ σ topLabelN)
    (hnal : ¬ (ChordSep A B C ∨ ChordSep B A C ∨ ChordSep C A B)) : False := by
  obtain ⟨xa, ya, hsa, hlea, rfl⟩ := mem_kChords.mp hA
  obtain ⟨xb, yb, hsb, hleb, rfl⟩ := mem_kChords.mp hB
  obtain ⟨xc, yc, hsc, hlec, rfl⟩ := mem_kChords.mp hC
  haveI : NeZero (N - 1) := ⟨by omega⟩
  have htopv : (topLabelN : ZMod N).val = N - 1 := topLabelN_val
  have hA2 : ya.val < N - 1 := by
    have h := hnotop.1
    have h2 : ya ≠ topLabelN := fun he => h (by rw [he])
    have h3 : ya.val ≠ (topLabelN : ZMod N).val := fun he => h2 (ZMod.val_injective _ he)
    rw [htopv] at h3
    have := ZMod.val_lt ya
    omega
  have hB2 : yb.val < N - 1 := by
    have h := hnotop.2.1
    have h2 : yb ≠ topLabelN := fun he => h (by rw [he])
    have h3 : yb.val ≠ (topLabelN : ZMod N).val := fun he => h2 (ZMod.val_injective _ he)
    rw [htopv] at h3
    have := ZMod.val_lt yb
    omega
  have hC2 : yc.val < N - 1 := by
    have h := hnotop.2.2
    have h2 : yc ≠ topLabelN := fun he => h (by rw [he])
    have h3 : yc.val ≠ (topLabelN : ZMod N).val := fun he => h2 (ZMod.val_injective _ he)
    rw [htopv] at h3
    have := ZMod.val_lt yc
    omega
  have hA1 : xa.val < N - 1 := by have := hA2; omega
  have hB1 : xb.val < N - 1 := by have := hB2; omega
  have hC1 : xc.val < N - 1 := by have := hC2; omega
  have hDelB : Beautiful (DelN σ) := DelN_beautiful hσ
  have hcast : ∀ x : ZMod N, x.val < N - 1 → (((x.val : ℕ) : ZMod (N - 1))).val = x.val := by
    intro x hx
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hx]
  have hli : ∀ x : ZMod N, x.val < N - 1 → labelInclN ((x.val : ℕ) : ZMod (N - 1)) = x := by
    intro x hx
    show (↑(((x.val : ℕ) : ZMod (N - 1)).val) : ZMod N) = x
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hx, ZMod.natCast_zmod_val]
  have hex : ∀ x : ZMod N, x.val < N - 1 →
      circleInclN (σ topLabelN) ((DelN σ) ((x.val : ℕ) : ZMod (N - 1))) = σ x := by
    intro x hx
    set y : {z : ZMod N // z ≠ σ topLabelN} :=
      ⟨σ (labelInclN ((x.val : ℕ) : ZMod (N - 1))),
        (Equiv.apply_eq_iff_eq σ).not.mpr (labelInclN_ne_top _)⟩ with hy
    have e1 : (DelN σ) ((x.val : ℕ) : ZMod (N - 1)) = cutCircleN (σ topLabelN) y := by
      apply ZMod.val_injective (N - 1)
      rfl
    rw [e1, circleInclN_cutCircleN, hy]
    show σ (labelInclN ((x.val : ℕ) : ZMod (N - 1))) = σ x
    rw [hli x hx]
  have hinj : ∀ x y : ZMod N, x.val < N - 1 → y.val < N - 1 →
      (DelN σ) ((x.val : ℕ) : ZMod (N - 1)) = (DelN σ) ((y.val : ℕ) : ZMod (N - 1)) → x = y := by
    intro x y hx hy he
    have h1 : σ x = σ y := by
      have h2 := congrArg (circleInclN (σ topLabelN)) he
      rwa [hex x hx, hex y hy] at h2
    have h3 : x = y := σ.injective h1
    exact h3
  have hAmem : ((DelN σ) ((xa.val : ℕ) : ZMod (N - 1)), (DelN σ) ((ya.val : ℕ) : ZMod (N - 1))) ∈
      kChords (DelN σ) k := by
    rw [mem_kChords]
    exact ⟨_, _, by rw [hcast _ hA1, hcast _ hA2]; exact hsa, by
      rw [hcast _ hA1, hcast _ hA2]; exact hlea, rfl⟩
  have hBmem : ((DelN σ) ((xb.val : ℕ) : ZMod (N - 1)), (DelN σ) ((yb.val : ℕ) : ZMod (N - 1))) ∈
      kChords (DelN σ) k := by
    rw [mem_kChords]
    exact ⟨_, _, by rw [hcast _ hB1, hcast _ hB2]; exact hsb, by
      rw [hcast _ hB1, hcast _ hB2]; exact hleb, rfl⟩
  have hCmem : ((DelN σ) ((xc.val : ℕ) : ZMod (N - 1)), (DelN σ) ((yc.val : ℕ) : ZMod (N - 1))) ∈
      kChords (DelN σ) k := by
    rw [mem_kChords]
    exact ⟨_, _, by rw [hcast _ hC1, hcast _ hC2]; exact hsc, by
      rw [hcast _ hC1, hcast _ hC2]; exact hlec, rfl⟩
  have hAB' : ((DelN σ) ((xa.val : ℕ) : ZMod (N - 1)), (DelN σ) ((ya.val : ℕ) : ZMod (N - 1))) ≠
      ((DelN σ) ((xb.val : ℕ) : ZMod (N - 1)), (DelN σ) ((yb.val : ℕ) : ZMod (N - 1))) := by
    intro he
    obtain ⟨h1, h2⟩ := Prod.ext_iff.mp he
    have e1 : xa = xb := hinj xa xb hA1 hB1 h1
    have e2 : ya = yb := hinj ya yb hA2 hB2 h2
    rw [e1, e2] at hAB
    exact hAB rfl
  have hBC' : ((DelN σ) ((xb.val : ℕ) : ZMod (N - 1)), (DelN σ) ((yb.val : ℕ) : ZMod (N - 1))) ≠
      ((DelN σ) ((xc.val : ℕ) : ZMod (N - 1)), (DelN σ) ((yc.val : ℕ) : ZMod (N - 1))) := by
    intro he
    obtain ⟨h1, h2⟩ := Prod.ext_iff.mp he
    have e1 : xb = xc := hinj xb xc hB1 hC1 h1
    have e2 : yb = yc := hinj yb yc hB2 hC2 h2
    rw [e1, e2] at hBC
    exact hBC rfl
  have hAC' : ((DelN σ) ((xa.val : ℕ) : ZMod (N - 1)), (DelN σ) ((ya.val : ℕ) : ZMod (N - 1))) ≠
      ((DelN σ) ((xc.val : ℕ) : ZMod (N - 1)), (DelN σ) ((yc.val : ℕ) : ZMod (N - 1))) := by
    intro he
    obtain ⟨h1, h2⟩ := Prod.ext_iff.mp he
    have e1 : xa = xc := hinj xa xc hA1 hC1 h1
    have e2 : ya = yc := hinj ya yc hA2 hC2 h2
    rw [e1, e2] at hAC
    exact hAC rfl
  have dAB := hdj _ hA _ hB hAB
  have dBC := hdj _ hB _ hC hBC
  have dAC := hdj _ hA _ hC hAC
  have hih := ih (N - 1) (by omega) (DelN σ) hDelB k
    ((DelN σ) ((xa.val : ℕ) : ZMod (N - 1)), (DelN σ) ((ya.val : ℕ) : ZMod (N - 1))) hAmem
    ((DelN σ) ((xb.val : ℕ) : ZMod (N - 1)), (DelN σ) ((yb.val : ℕ) : ZMod (N - 1))) hBmem
    ((DelN σ) ((xc.val : ℕ) : ZMod (N - 1)), (DelN σ) ((yc.val : ℕ) : ZMod (N - 1))) hCmem
    hAB' hBC' hAC'
  have htr1 := (ChordSep.circleInclN (q := σ topLabelN)
    (A := ((DelN σ) ((xa.val : ℕ) : ZMod (N - 1)), (DelN σ) ((ya.val : ℕ) : ZMod (N - 1))))
    (B := ((DelN σ) ((xb.val : ℕ) : ZMod (N - 1)), (DelN σ) ((yb.val : ℕ) : ZMod (N - 1))))
    (C := ((DelN σ) ((xc.val : ℕ) : ZMod (N - 1)), (DelN σ) ((yc.val : ℕ) : ZMod (N - 1))))
    (fun he => dAB.1 (congrArg σ (hinj xa xb hA1 hB1 he)))
    (fun he => dAB.2.1 (congrArg σ (hinj xa yb hA1 hB2 he)))
    (fun he => dAC.1 (congrArg σ (hinj xa xc hA1 hC1 he)))
    (fun he => dAC.2.1 (congrArg σ (hinj xa yc hA1 hC2 he))))
  rw [hex xa hA1, hex ya hA2, hex xb hB1, hex yb hB2, hex xc hC1, hex yc hC2] at htr1
  have htr2 := (ChordSep.circleInclN (q := σ topLabelN)
    (A := ((DelN σ) ((xb.val : ℕ) : ZMod (N - 1)), (DelN σ) ((yb.val : ℕ) : ZMod (N - 1))))
    (B := ((DelN σ) ((xa.val : ℕ) : ZMod (N - 1)), (DelN σ) ((ya.val : ℕ) : ZMod (N - 1))))
    (C := ((DelN σ) ((xc.val : ℕ) : ZMod (N - 1)), (DelN σ) ((yc.val : ℕ) : ZMod (N - 1))))
    (fun he => dAB.1.symm (congrArg σ (hinj xb xa hB1 hA1 he)))
    (fun he => dAB.2.2.1.symm (congrArg σ (hinj xb ya hB1 hA2 he)))
    (fun he => dBC.1 (congrArg σ (hinj xb xc hB1 hC1 he)))
    (fun he => dBC.2.1 (congrArg σ (hinj xb yc hB1 hC2 he))))
  rw [hex xb hB1, hex yb hB2, hex xa hA1, hex ya hA2, hex xc hC1, hex yc hC2] at htr2
  have htr3 := (ChordSep.circleInclN (q := σ topLabelN)
    (A := ((DelN σ) ((xc.val : ℕ) : ZMod (N - 1)), (DelN σ) ((yc.val : ℕ) : ZMod (N - 1))))
    (B := ((DelN σ) ((xa.val : ℕ) : ZMod (N - 1)), (DelN σ) ((ya.val : ℕ) : ZMod (N - 1))))
    (C := ((DelN σ) ((xb.val : ℕ) : ZMod (N - 1)), (DelN σ) ((yb.val : ℕ) : ZMod (N - 1))))
    (fun he => dAC.1.symm (congrArg σ (hinj xc xa hC1 hA1 he)))
    (fun he => dAC.2.2.1.symm (congrArg σ (hinj xc ya hC1 hA2 he)))
    (fun he => dBC.1.symm (congrArg σ (hinj xc xb hC1 hB1 he)))
    (fun he => dBC.2.2.1.symm (congrArg σ (hinj xc yb hC1 hB2 he))))
  rw [hex xc hC1, hex yc hC2, hex xa hA1, hex ya hA2, hex xb hB1, hex yb hB2] at htr3
  obtain h1 | h2 | h3 := hih
  · exact hnal (Or.inl (htr1.mpr h1))
  · exact hnal (Or.inr (Or.inl (htr2.mpr h2)))
  · exact hnal (Or.inr (Or.inr (htr3.mpr h3)))

theorem aligned_step_delzero {N : ℕ} [NeZero N] [NeZero (N - 1)] {σ : ZMod N ≃ ZMod N}
    (hN : 4 ≤ N) (hσ : Beautiful σ)
    (ih : ∀ M < N, ∀ [NeZero M], ∀ σ' : ZMod M ≃ ZMod M, Beautiful σ' →
      ∀ k : ℕ, ChordAligned (kChords σ' k))
    {k : ℕ} {A B C : Chord N} (hA : A ∈ kChords σ k) (hB : B ∈ kChords σ k)
    (hC : C ∈ kChords σ k) (hAB : A ≠ B) (hBC : B ≠ C) (hAC : A ≠ C)
    (hdj : ChordDisjoint (kChords σ k))
    (hnozero : A.1 ≠ σ (0 : ZMod N) ∧ B.1 ≠ σ (0 : ZMod N) ∧ C.1 ≠ σ (0 : ZMod N))
    (hnal : ¬ (ChordSep A B C ∨ ChordSep B A C ∨ ChordSep C A B)) : False := by
  obtain ⟨xa, ya, hsa, hlea, rfl⟩ := mem_kChords.mp hA
  obtain ⟨xb, yb, hsb, hleb, rfl⟩ := mem_kChords.mp hB
  obtain ⟨xc, yc, hsc, hlec, rfl⟩ := mem_kChords.mp hC
  haveI : NeZero (N - 1) := ⟨by omega⟩
  have htopv : ((0 : ZMod N) : ZMod N).val = 0 := ZMod.val_zero
  have hA1 : 1 ≤ xa.val := by
    have h := hnozero.1
    have h2 : xa ≠ (0 : ZMod N) := fun he => h (by rw [he])
    have h3 : xa.val ≠ ((0 : ZMod N) : ZMod N).val := fun he => h2 (ZMod.val_injective _ he)
    rw [htopv] at h3
    omega
  have hB1 : 1 ≤ xb.val := by
    have h := hnozero.2.1
    have h2 : xb ≠ (0 : ZMod N) := fun he => h (by rw [he])
    have h3 : xb.val ≠ ((0 : ZMod N) : ZMod N).val := fun he => h2 (ZMod.val_injective _ he)
    rw [htopv] at h3
    omega
  have hC1 : 1 ≤ xc.val := by
    have h := hnozero.2.2
    have h2 : xc ≠ (0 : ZMod N) := fun he => h (by rw [he])
    have h3 : xc.val ≠ ((0 : ZMod N) : ZMod N).val := fun he => h2 (ZMod.val_injective _ he)
    rw [htopv] at h3
    omega
  have hA2 : 1 ≤ ya.val := by omega
  have hB2 : 1 ≤ yb.val := by omega
  have hC2 : 1 ≤ yc.val := by omega
  have hDelB : Beautiful (DelZeroN σ) := DelZeroN_beautiful hσ
  have hcast : ∀ x : ZMod N, 1 ≤ x.val → (((x.val - 1 : ℕ) : ZMod (N - 1))).val = x.val - 1 := by
    intro x hx
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by have := ZMod.val_lt x; omega : x.val - 1 < N - 1)]
  have hex : ∀ x : ZMod N, 1 ≤ x.val →
      circleInclN (σ (0 : ZMod N)) ((DelZeroN σ) ((x.val - 1 : ℕ) : ZMod (N - 1))) = σ x := by
    intro x hx
    have e1 : (DelZeroN σ) ((x.val - 1 : ℕ) : ZMod (N - 1)) =
        cutCircleN (σ (0 : ZMod N)) ⟨σ ((x.val : ℕ) : ZMod N),
          (Equiv.apply_eq_iff_eq σ).not.mpr (by
            intro h
            have h1 : (((x.val : ℕ) : ZMod N)).val = (0 : ZMod N).val := by rw [h]
            rw [ZMod.val_natCast, Nat.mod_eq_of_lt (ZMod.val_lt x), ZMod.val_zero] at h1
            omega)⟩ := by
      apply ZMod.val_injective (N - 1)
      simp only [DelZeroN, Equiv.trans_apply, Equiv.subtypeEquiv_apply, succLabelEquivN,
        Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk, circleIsoN]
      rw [hcast x hx]
      have e3 : x.val - 1 + 1 = x.val := by omega
      rw [e3]
      rfl
    rw [e1, circleInclN_cutCircleN]
    show σ ((x.val : ℕ) : ZMod N) = σ x
    rw [ZMod.natCast_zmod_val]
  have hinj : ∀ x y : ZMod N, 1 ≤ x.val → 1 ≤ y.val →
      (DelZeroN σ) ((x.val - 1 : ℕ) : ZMod (N - 1)) = (DelZeroN σ) ((y.val - 1 : ℕ) : ZMod (N - 1)) → x = y := by
    intro x y hx hy he
    have h1 : σ x = σ y := by
      have h2 := congrArg (circleInclN (σ (0 : ZMod N))) he
      rwa [hex x hx, hex y hy] at h2
    have h3 : x = y := σ.injective h1
    exact h3
  have hAmem : ((DelZeroN σ) ((xa.val - 1 : ℕ) : ZMod (N - 1)), (DelZeroN σ) ((ya.val - 1 : ℕ) : ZMod (N - 1))) ∈
      kChords (DelZeroN σ) (k - 2) := by
    rw [mem_kChords]
    exact ⟨_, _, by rw [hcast _ hA1, hcast _ hA2]; omega, by
      rw [hcast _ hA1, hcast _ hA2]; omega, rfl⟩
  have hBmem : ((DelZeroN σ) ((xb.val - 1 : ℕ) : ZMod (N - 1)), (DelZeroN σ) ((yb.val - 1 : ℕ) : ZMod (N - 1))) ∈
      kChords (DelZeroN σ) (k - 2) := by
    rw [mem_kChords]
    exact ⟨_, _, by rw [hcast _ hB1, hcast _ hB2]; omega, by
      rw [hcast _ hB1, hcast _ hB2]; omega, rfl⟩
  have hCmem : ((DelZeroN σ) ((xc.val - 1 : ℕ) : ZMod (N - 1)), (DelZeroN σ) ((yc.val - 1 : ℕ) : ZMod (N - 1))) ∈
      kChords (DelZeroN σ) (k - 2) := by
    rw [mem_kChords]
    exact ⟨_, _, by rw [hcast _ hC1, hcast _ hC2]; omega, by
      rw [hcast _ hC1, hcast _ hC2]; omega, rfl⟩
  have hAB' : ((DelZeroN σ) ((xa.val - 1 : ℕ) : ZMod (N - 1)), (DelZeroN σ) ((ya.val - 1 : ℕ) : ZMod (N - 1))) ≠
      ((DelZeroN σ) ((xb.val - 1 : ℕ) : ZMod (N - 1)), (DelZeroN σ) ((yb.val - 1 : ℕ) : ZMod (N - 1))) := by
    intro he
    obtain ⟨h1, h2⟩ := Prod.ext_iff.mp he
    have e1 : xa = xb := hinj xa xb hA1 hB1 h1
    have e2 : ya = yb := hinj ya yb hA2 hB2 h2
    rw [e1, e2] at hAB
    exact hAB rfl
  have hBC' : ((DelZeroN σ) ((xb.val - 1 : ℕ) : ZMod (N - 1)), (DelZeroN σ) ((yb.val - 1 : ℕ) : ZMod (N - 1))) ≠
      ((DelZeroN σ) ((xc.val - 1 : ℕ) : ZMod (N - 1)), (DelZeroN σ) ((yc.val - 1 : ℕ) : ZMod (N - 1))) := by
    intro he
    obtain ⟨h1, h2⟩ := Prod.ext_iff.mp he
    have e1 : xb = xc := hinj xb xc hB1 hC1 h1
    have e2 : yb = yc := hinj yb yc hB2 hC2 h2
    rw [e1, e2] at hBC
    exact hBC rfl
  have hAC' : ((DelZeroN σ) ((xa.val - 1 : ℕ) : ZMod (N - 1)), (DelZeroN σ) ((ya.val - 1 : ℕ) : ZMod (N - 1))) ≠
      ((DelZeroN σ) ((xc.val - 1 : ℕ) : ZMod (N - 1)), (DelZeroN σ) ((yc.val - 1 : ℕ) : ZMod (N - 1))) := by
    intro he
    obtain ⟨h1, h2⟩ := Prod.ext_iff.mp he
    have e1 : xa = xc := hinj xa xc hA1 hC1 h1
    have e2 : ya = yc := hinj ya yc hA2 hC2 h2
    rw [e1, e2] at hAC
    exact hAC rfl
  have dAB := hdj _ hA _ hB hAB
  have dBC := hdj _ hB _ hC hBC
  have dAC := hdj _ hA _ hC hAC
  have hih := ih (N - 1) (by omega) (DelZeroN σ) hDelB (k - 2)
    ((DelZeroN σ) ((xa.val - 1 : ℕ) : ZMod (N - 1)), (DelZeroN σ) ((ya.val - 1 : ℕ) : ZMod (N - 1))) hAmem
    ((DelZeroN σ) ((xb.val - 1 : ℕ) : ZMod (N - 1)), (DelZeroN σ) ((yb.val - 1 : ℕ) : ZMod (N - 1))) hBmem
    ((DelZeroN σ) ((xc.val - 1 : ℕ) : ZMod (N - 1)), (DelZeroN σ) ((yc.val - 1 : ℕ) : ZMod (N - 1))) hCmem
    hAB' hBC' hAC'
  have htr1 := (ChordSep.circleInclN (q := σ (0 : ZMod N))
    (A := ((DelZeroN σ) ((xa.val - 1 : ℕ) : ZMod (N - 1)), (DelZeroN σ) ((ya.val - 1 : ℕ) : ZMod (N - 1))))
    (B := ((DelZeroN σ) ((xb.val - 1 : ℕ) : ZMod (N - 1)), (DelZeroN σ) ((yb.val - 1 : ℕ) : ZMod (N - 1))))
    (C := ((DelZeroN σ) ((xc.val - 1 : ℕ) : ZMod (N - 1)), (DelZeroN σ) ((yc.val - 1 : ℕ) : ZMod (N - 1))))
    (fun he => dAB.1 (congrArg σ (hinj xa xb hA1 hB1 he)))
    (fun he => dAB.2.1 (congrArg σ (hinj xa yb hA1 hB2 he)))
    (fun he => dAC.1 (congrArg σ (hinj xa xc hA1 hC1 he)))
    (fun he => dAC.2.1 (congrArg σ (hinj xa yc hA1 hC2 he))))
  rw [hex xa hA1, hex ya hA2, hex xb hB1, hex yb hB2, hex xc hC1, hex yc hC2] at htr1
  have htr2 := (ChordSep.circleInclN (q := σ (0 : ZMod N))
    (A := ((DelZeroN σ) ((xb.val - 1 : ℕ) : ZMod (N - 1)), (DelZeroN σ) ((yb.val - 1 : ℕ) : ZMod (N - 1))))
    (B := ((DelZeroN σ) ((xa.val - 1 : ℕ) : ZMod (N - 1)), (DelZeroN σ) ((ya.val - 1 : ℕ) : ZMod (N - 1))))
    (C := ((DelZeroN σ) ((xc.val - 1 : ℕ) : ZMod (N - 1)), (DelZeroN σ) ((yc.val - 1 : ℕ) : ZMod (N - 1))))
    (fun he => dAB.1.symm (congrArg σ (hinj xb xa hB1 hA1 he)))
    (fun he => dAB.2.2.1.symm (congrArg σ (hinj xb ya hB1 hA2 he)))
    (fun he => dBC.1 (congrArg σ (hinj xb xc hB1 hC1 he)))
    (fun he => dBC.2.1 (congrArg σ (hinj xb yc hB1 hC2 he))))
  rw [hex xb hB1, hex yb hB2, hex xa hA1, hex ya hA2, hex xc hC1, hex yc hC2] at htr2
  have htr3 := (ChordSep.circleInclN (q := σ (0 : ZMod N))
    (A := ((DelZeroN σ) ((xc.val - 1 : ℕ) : ZMod (N - 1)), (DelZeroN σ) ((yc.val - 1 : ℕ) : ZMod (N - 1))))
    (B := ((DelZeroN σ) ((xa.val - 1 : ℕ) : ZMod (N - 1)), (DelZeroN σ) ((ya.val - 1 : ℕ) : ZMod (N - 1))))
    (C := ((DelZeroN σ) ((xb.val - 1 : ℕ) : ZMod (N - 1)), (DelZeroN σ) ((yb.val - 1 : ℕ) : ZMod (N - 1))))
    (fun he => dAC.1.symm (congrArg σ (hinj xc xa hC1 hA1 he)))
    (fun he => dAC.2.2.1.symm (congrArg σ (hinj xc ya hC1 hA2 he)))
    (fun he => dBC.1.symm (congrArg σ (hinj xc xb hC1 hB1 he)))
    (fun he => dBC.2.2.1.symm (congrArg σ (hinj xc yb hC1 hB2 he))))
  rw [hex xc hC1, hex yc hC2, hex xa hA1, hex ya hA2, hex xb hB1, hex yb hB2] at htr3
  obtain h1 | h2 | h3 := hih
  · exact hnal (Or.inl (htr1.mpr h1))
  · exact hnal (Or.inr (Or.inl (htr2.mpr h2)))
  · exact hnal (Or.inr (Or.inr (htr3.mpr h3)))

/-- The number of canonical `k`-chords is at most the number of possible smaller
endpoints. -/
theorem kChords_card_le {N : ℕ} [NeZero N] (σ : ZMod N ≃ ZMod N) (k : ℕ) :
    (kChords σ k).card ≤ (Finset.Icc (k - (N - 1)) (k / 2)).card := by
  have h1 : (kChords σ k).card =
      ((Finset.univ ×ˢ Finset.univ).filter fun p : ZMod N × ZMod N =>
        p.1.val + p.2.val = k ∧ p.1.val ≤ p.2.val).card := by
    have hinj : Function.Injective fun p : ZMod N × ZMod N => (σ p.1, σ p.2) := by
      intro p q h
      rw [Prod.ext_iff] at h
      exact Prod.ext (σ.injective h.1) (σ.injective h.2)
    unfold kChords
    rw [Finset.card_image_of_injective _ hinj]
  rw [h1]
  apply Finset.card_le_card_of_injOn (fun p : ZMod N × ZMod N => p.1.val)
  · intro p hp
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hp
    show p.1.val ∈ ↑(Icc (k - (N - 1)) (k / 2))
    rw [Finset.mem_Icc]
    have h2 := ZMod.val_lt p.2
    constructor <;> omega
  · intro p hp q hq he
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hp hq
    have he' : p.1.val = q.1.val := he
    have h2 : p.2 = q.2 := ZMod.val_injective _ (by omega)
    exact Prod.ext (ZMod.val_injective _ he') h2

/-- For arrangements of `[0, N - 1]` with `N ≤ 3` there are at most two
`k`-chords. -/
theorem kChords_card_le_two {N : ℕ} [NeZero N] (hN : N ≤ 3) (σ : ZMod N ≃ ZMod N)
    (k : ℕ) : (kChords σ k).card ≤ 2 := by
  have h := kChords_card_le σ k
  rw [Nat.card_Icc] at h
  have : k / 2 + 1 - (k - (N - 1)) ≤ 2 := by omega
  omega

/-- A family of at most two chords is trivially aligned. -/
theorem ChordAligned.of_card_le_two {N : ℕ} [NeZero N] {F : Finset (Chord N)} (hF : F.card ≤ 2) :
    ChordAligned F := by
  intro A hA B hB C hC hAB hBC hAC
  exfalso
  have h3 : 3 ≤ F.card := by
    have hsub : ({A, B, C} : Finset (Chord N)) ⊆ F := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact hA
      · exact hB
      · exact hC
    have hcard : ({A, B, C} : Finset (Chord N)).card = 3 := by
      rw [Finset.card_insert_of_notMem (by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨hAB, hAC⟩),
        Finset.card_insert_of_notMem (by
          simp only [Finset.mem_singleton]
          exact hBC),
        Finset.card_singleton]
    rw [← hcard]
    exact Finset.card_le_card hsub
  omega

theorem Beautiful.nonCross_four {N : ℕ} [NeZero N] {σ : ZMod N ≃ ZMod N} (h : Beautiful σ)
    {w x y z : ZMod N} (h1 : w.val < x.val) (h2 : x.val < y.val) (h3 : y.val < z.val)
    (hsum : w.val + z.val = x.val + y.val) :
    (sbtw (σ w) (σ x) (σ z) ↔ sbtw (σ w) (σ y) (σ z)) ∧
    (sbtw (σ x) (σ w) (σ y) ↔ sbtw (σ x) (σ z) (σ y)) := by
  have hb := h w x y z h1 h2 h3 hsum
  unfold Crossing at hb
  have hb' : (sbtw (σ w) (σ x) (σ z) ↔ sbtw (σ w) (σ y) (σ z)) := by
    rw [show sbtw (σ w) (σ x) (σ z) = sbtw (σ w) (σ y) (σ z) from not_not.mp hb]
  refine ⟨hb', ?_⟩
  have di : ∀ u v : ZMod N, u.val < v.val → σ u ≠ σ v := by
    intro u v huv he
    rw [σ.injective he] at huv
    exact absurd huv (lt_irrefl _)
  have dwx := di w x h1
  have dwy := di w y (h1.trans h2)
  have dwz := di w z ((h1.trans h2).trans h3)
  have dxz := di x z (h2.trans h3)
  rw [sbtw_val dwx, sbtw_val dwy] at hb'
  rw [sbtw_val dwx.symm, sbtw_val dxz]
  rw [val_sub_if (σ x) (σ w), val_sub_if (σ x) (σ y), val_sub_if (σ x) (σ z)]
  rw [val_sub_if (σ w) (σ x), val_sub_if (σ w) (σ y), val_sub_if (σ w) (σ z)] at hb'
  have hw := ZMod.val_lt (σ w); have hx := ZMod.val_lt (σ x)
  have hy := ZMod.val_lt (σ y); have hz := ZMod.val_lt (σ z)
  have d1 : (σ w).val ≠ (σ x).val := fun he => dwx (ZMod.val_injective _ he)
  have d2 : (σ w).val ≠ (σ y).val := fun he => dwy (ZMod.val_injective _ he)
  have d3 : (σ w).val ≠ (σ z).val := fun he => dwz (ZMod.val_injective _ he)
  have d4 : (σ x).val ≠ (σ y).val := fun he => (di x y h2) (ZMod.val_injective _ he)
  have d5 : (σ x).val ≠ (σ z).val := fun he => dxz (ZMod.val_injective _ he)
  have d6 : (σ y).val ≠ (σ z).val := fun he => (di y z h3) (ZMod.val_injective _ he)
  split_ifs at hb' ⊢ <;> omega

/-- Beautiful arrangements have pairwise non-crossing same-sum chords. -/
theorem Beautiful.kChords_nonCrossing {N : ℕ} [NeZero N] {σ : ZMod N ≃ ZMod N}
    (h : Beautiful σ) (k : ℕ) : ChordNonCrossing (kChords σ k) := by
  intro A hA B hB hne
  rw [mem_kChords] at hA hB
  obtain ⟨xa, ya, hsa, hlea, rfl⟩ := hA
  obtain ⟨xb, yb, hsb, hleb, rfl⟩ := hB
  have hsum : xa.val + ya.val = xb.val + yb.val := by omega
  rcases lt_trichotomy xa.val xb.val with h1 | h1 | h1
  · have hya : yb.val < ya.val := by omega
    rcases eq_or_ne xb yb with h2 | h2
    · subst h2
      exact Iff.rfl
    · have h2' : xb.val < yb.val :=
        lt_of_le_of_ne hleb (fun he => h2 (ZMod.val_injective _ he))
      exact (h.nonCross_four h1 h2' hya (by omega)).1
  · have hx : xa = xb := ZMod.val_injective _ h1
    have hy : ya = yb := ZMod.val_injective _ (by omega)
    subst hx; subst hy
    exact absurd rfl hne
  · have hya : ya.val < yb.val := by omega
    rcases eq_or_ne xa ya with h2 | h2
    · subst h2
      exact ⟨fun h' => absurd h' sbtw_irrefl_left_right,
        fun h' => absurd h' sbtw_irrefl_left_right⟩
    · have h2' : xa.val < ya.val :=
        lt_of_le_of_ne hlea (fun he => h2 (ZMod.val_injective _ he))
      exact (h.nonCross_four (by omega : xb.val < xa.val) h2' (by omega : ya.val < yb.val)
        (by omega)).2


/-- Swapping the endpoints of the first chord preserves crossing (for distinct
endpoints). -/
theorem Crossing.swap {N : ℕ} [NeZero N] {p q r s : ZMod N} (hpr : p ≠ r) (hrq : r ≠ q)
    (hqp : q ≠ p) (hps : p ≠ s) (hsq : s ≠ q) :
    Crossing p q r s ↔ Crossing q p r s := by
  unfold Crossing
  rw [sbtw_not_reverse hpr hrq hqp, sbtw_not_reverse hps hsq hqp]
  constructor
  · intro h1 h2
    exact h1 (congrArg Not h2)
  · intro h1 h2
    apply h1
    by_cases hX : sbtw q r p <;> by_cases hY : sbtw q s p <;> simp [hX, hY] at h2 ⊢

/-- The label-reversing involution `x ↦ m - x` on `[0, m]`, used to reduce the
`t > m` case of the main claim to the `t < m` case. -/
def negLabelEquiv {N : ℕ} [NeZero N] : ZMod N ≃ ZMod N where
  toFun x := ((N - 1 - x.val : ℕ) : ZMod N)
  invFun x := ((N - 1 - x.val : ℕ) : ZMod N)
  left_inv x := by
    show ((N - 1 - (((N - 1 - x.val : ℕ) : ZMod N)).val : ℕ) : ZMod N) = x
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by have := ZMod.val_lt x; omega : N - 1 - x.val < N)]
    have := ZMod.val_lt x
    rw [show N - 1 - (N - 1 - x.val) = x.val from by omega, ZMod.natCast_zmod_val]
  right_inv x := by
    show ((N - 1 - (((N - 1 - x.val : ℕ) : ZMod N)).val : ℕ) : ZMod N) = x
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by have := ZMod.val_lt x; omega : N - 1 - x.val < N)]
    have := ZMod.val_lt x
    rw [show N - 1 - (N - 1 - x.val) = x.val from by omega, ZMod.natCast_zmod_val]

theorem negLabel_val {N : ℕ} [NeZero N] (x : ZMod N) :
    (negLabelEquiv x).val = N - 1 - x.val := by
  show (((N - 1 - x.val : ℕ) : ZMod N)).val = N - 1 - x.val
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by have := ZMod.val_lt x; omega : N - 1 - x.val < N)]

/-- Swapping the endpoints of the second chord preserves crossing. -/
theorem Crossing.swap' {N : ℕ} [NeZero N] {P Q R S : ZMod N} :
    Crossing P Q R S ↔ Crossing P Q S R := by
  unfold Crossing
  rw [ne_comm]

/-- Swapping the endpoints of both chords preserves crossing (for distinct
endpoints). -/
theorem Crossing.swap_both {N : ℕ} [NeZero N] {P Q R S : ZMod N}
    (hPR : P ≠ R) (hRQ : R ≠ Q) (hQP : Q ≠ P) (hPS : P ≠ S) (hSQ : S ≠ Q) :
    Crossing P Q R S ↔ Crossing Q P S R := by
  rw [Crossing.swap hPR hRQ hQP hPS hSQ, Crossing.swap']

/-- Beauty is preserved under the label-reversing involution. -/
theorem Beautiful.negLabel {N : ℕ} [NeZero N] {σ : ZMod N ≃ ZMod N} (h : Beautiful σ) :
    Beautiful (negLabelEquiv.trans σ) := by
  intro a b c d hab hbc hcd hsum hc
  have hval : ∀ x : ZMod N, (negLabelEquiv x).val = N - 1 - x.val := negLabel_val
  have dne : ∀ x y : ZMod N, x.val < y.val → σ (negLabelEquiv x) ≠ σ (negLabelEquiv y) := by
    intro x y hxy he
    have h1 : negLabelEquiv x = negLabelEquiv y := σ.injective he
    have h2 : x = y := negLabelEquiv.injective h1
    rw [h2] at hxy
    exact absurd hxy (lt_irrefl _)
  have hS := h (negLabelEquiv d) (negLabelEquiv c) (negLabelEquiv b) (negLabelEquiv a)
    (by rw [hval, hval]; have h1 := ZMod.val_lt a; have h2 := ZMod.val_lt d; omega)
    (by rw [hval, hval]; have h1 := ZMod.val_lt b; have h2 := ZMod.val_lt c; omega)
    (by rw [hval, hval]; have h1 := ZMod.val_lt a; have h2 := ZMod.val_lt b; omega)
    (by rw [hval, hval, hval, hval]; have h1 := ZMod.val_lt a; have h2 := ZMod.val_lt d; omega)
  apply hS
  have hc' : Crossing (σ (negLabelEquiv a)) (σ (negLabelEquiv d)) (σ (negLabelEquiv b))
      (σ (negLabelEquiv c)) := hc
  exact (Crossing.swap_both ((dne c d hcd).symm) ((dne a c (hab.trans hbc)).symm)
    (dne a d (by omega)) ((dne b d (hbc.trans hcd)).symm) ((dne a b hab).symm)).mpr hc'


/-! ## Arc geometry in `θ`-coordinates -/

/-- Master reduction: strict betweenness of three points, none equal to the base
point `q₀`, as a disjunction of `θ = (· - q₀).val` comparisons. -/
theorem sbtw_theta {N : ℕ} [NeZero N] {q₀ x y z : ZMod N}
    (hx : x ≠ q₀) (hy : y ≠ q₀) (hz : z ≠ q₀) (hxy : x ≠ y) (hyz : y ≠ z) (hzx : z ≠ x) :
    sbtw x y z ↔ ((x - q₀).val < (y - q₀).val ∧ (y - q₀).val < (z - q₀).val) ∨
      ((y - q₀).val < (z - q₀).val ∧ (z - q₀).val < (x - q₀).val) ∨
      ((z - q₀).val < (x - q₀).val ∧ (x - q₀).val < (y - q₀).val) := by
  rw [sbtw_val hxy]
  have e1 : y - x = (y - q₀) - (x - q₀) := by ring
  have e2 : z - x = (z - q₀) - (x - q₀) := by ring
  rw [e1, e2, val_sub' (y - q₀) (x - q₀), val_sub' (z - q₀) (x - q₀)]
  have hθ : ∀ w : ZMod N, w ≠ q₀ → 0 < (w - q₀).val ∧ (w - q₀).val < N := by
    intro w hw
    have h1 := ZMod.val_lt (w - q₀)
    have h2 : (w - q₀).val ≠ 0 := by
      intro he
      apply hw
      have h3 : w - q₀ = 0 := by
        rw [← ZMod.natCast_zmod_val (w - q₀), he, Nat.cast_zero]
      exact sub_eq_zero.mp h3
    omega
  obtain ⟨hx0, hxN⟩ := hθ x hx
  obtain ⟨hy0, hyN⟩ := hθ y hy
  obtain ⟨hz0, hzN⟩ := hθ z hz
  have hinj : ∀ u v : ZMod N, u ≠ v → (u - q₀).val ≠ (v - q₀).val := by
    intro u v huv he
    apply huv
    have h1 : u - q₀ = v - q₀ := ZMod.val_injective _ he
    have h2 : u = v := by linear_combination h1
    exact h2
  have dxy := hinj x y hxy
  have dyz := hinj y z hyz
  have dzx := hinj z x hzx
  have key : ∀ a : ZMod N, ((a - q₀).val + N - (x - q₀).val) % N =
      if (x - q₀).val ≤ (a - q₀).val then (a - q₀).val - (x - q₀).val
      else (a - q₀).val + N - (x - q₀).val := by
    intro a
    have haN := ZMod.val_lt (a - q₀)
    by_cases ha : (x - q₀).val ≤ (a - q₀).val
    · rw [if_pos ha]
      have e : (a - q₀).val + N - (x - q₀).val = ((a - q₀).val - (x - q₀).val) + N := by
        omega
      rw [e, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : (a - q₀).val - (x - q₀).val < N)]
    · rw [if_neg ha, Nat.mod_eq_of_lt (by omega : (a - q₀).val + N - (x - q₀).val < N)]
  rw [key y, key z]
  by_cases h1 : (x - q₀).val ≤ (y - q₀).val <;> by_cases h2 : (x - q₀).val ≤ (z - q₀).val <;>
    simp [h1, h2] <;> omega


/-- `(· - q₀).val` is injective. -/

theorem theta_inj {N : ℕ} [NeZero N] {q₀ x y : ZMod N} (h : (x - q₀).val = (y - q₀).val) :
    x = y := by
  have h1 : x - q₀ = y - q₀ := ZMod.val_injective _ h
  linear_combination h1

/-- Points strictly between `q₀` and `q₁` have positive `θ` bounded by `θ q₁`. -/
theorem theta_mem {N : ℕ} [NeZero N] {q₀ q₁ x : ZMod N} (h : sbtw q₀ x q₁) :
    0 < (x - q₀).val ∧ (x - q₀).val < (q₁ - q₀).val := by
  have hq0x : q₀ ≠ x := by
    intro he
    rw [he] at h
    exact sbtw_irrefl_left h
  rw [sbtw_val hq0x] at h
  have h1 : (x - q₀).val ≠ 0 := by
    intro he
    apply hq0x
    have h2 : x - q₀ = 0 := by
      rw [← ZMod.natCast_zmod_val (x - q₀), he, Nat.cast_zero]
    exact (sub_eq_zero.mp h2).symm
  omega

/-- The value of a negation, generic modulus version. -/
theorem val_neg'' {N : ℕ} [NeZero N] {X : ZMod N} (hX : X ≠ 0) : (-X).val = N - X.val := by
  have h1 : X.val ≠ 0 := by
    intro he
    apply hX
    rw [← ZMod.natCast_zmod_val X, he, Nat.cast_zero]
  have h2 : (-X : ZMod N) = ((N - X.val : ℕ) : ZMod N) := by
    rw [neg_eq_iff_add_eq_zero]
    conv_lhs => congr; rw [← ZMod.natCast_zmod_val X]
    rw [← Nat.cast_add, show X.val + (N - X.val) = N from by
      have := ZMod.val_lt X; omega, ZMod.natCast_self]
  rw [h2, ZMod.val_natCast, Nat.mod_eq_of_lt (by have := ZMod.val_lt X; omega :
    N - X.val < N)]

/-- `sbtw x q₀ y` as a `θ` comparison. -/
theorem sbtw_mid_q₀ {N : ℕ} [NeZero N] {q₀ x y : ZMod N}
    (hx : x ≠ q₀) (hy : y ≠ q₀) (hxy : x ≠ y) :
    sbtw x q₀ y ↔ (y - q₀).val < (x - q₀).val := by
  rw [sbtw_val hx]
  have e1 : y - x = (y - q₀) - (x - q₀) := by ring
  rw [e1, val_sub' (y - q₀) (x - q₀)]
  have hxp : 0 < (x - q₀).val := by
    have h1 : (x - q₀).val ≠ 0 := by
      intro he
      apply hx
      have h2 : x - q₀ = 0 := by
        rw [← ZMod.natCast_zmod_val (x - q₀), he, Nat.cast_zero]
      exact sub_eq_zero.mp h2
    have := ZMod.val_lt (x - q₀); omega
  have hyp : 0 < (y - q₀).val := by
    have h1 : (y - q₀).val ≠ 0 := by
      intro he
      apply hy
      have h2 : y - q₀ = 0 := by
        rw [← ZMod.natCast_zmod_val (y - q₀), he, Nat.cast_zero]
      exact sub_eq_zero.mp h2
    have := ZMod.val_lt (y - q₀); omega
  have hxN := ZMod.val_lt (x - q₀)
  have hyN := ZMod.val_lt (y - q₀)
  have hq : (q₀ - x).val = N - (x - q₀).val := by
    have e : q₀ - x = -(x - q₀) := by ring
    rw [e, val_neg'' (sub_ne_zero.mpr hx)]
  rw [hq]
  have dxy : (x - q₀).val ≠ (y - q₀).val := fun h => hxy (theta_inj h)
  by_cases hle : (x - q₀).val ≤ (y - q₀).val
  · have e : ((y - q₀).val + N - (x - q₀).val) % N = (y - q₀).val - (x - q₀).val := by
      have e2 : (y - q₀).val + N - (x - q₀).val = ((y - q₀).val - (x - q₀).val) + N := by
        omega
      rw [e2, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : (y - q₀).val - (x - q₀).val < N)]
    rw [e]
    constructor <;> intro h <;> omega
  · have e : ((y - q₀).val + N - (x - q₀).val) % N = (y - q₀).val + N - (x - q₀).val :=
      Nat.mod_eq_of_lt (by omega : (y - q₀).val + N - (x - q₀).val < N)
    rw [e]
    constructor <;> intro h <;> omega

/-- `sbtw x y q₀` as a `θ` comparison. -/
theorem sbtw_last_q₀ {N : ℕ} [NeZero N] {q₀ x y : ZMod N}
    (hx : x ≠ q₀) (hy : y ≠ q₀) (hxy : x ≠ y) :
    sbtw x y q₀ ↔ (x - q₀).val < (y - q₀).val := by
  have h1 : sbtw x y q₀ ↔ ¬ sbtw q₀ y x := sbtw_not_reverse hxy hy (fun h => hx h.symm)
  rw [h1, sbtw_val (fun h => hy h.symm)]
  have hxy' : (x - q₀).val ≠ (y - q₀).val := fun h => hxy (theta_inj h)
  omega

/-- `ChordSep` is symmetric in the second and third chords. -/
theorem ChordSep.flip {N : ℕ} [NeZero N] (X Y Z : Chord N) :
    ChordSep X Y Z ↔ ChordSep X Z Y := by
  unfold ChordSep
  tauto




/-- Swapping both endpoints of every chord preserves `ChordSep` (given the eight
cross-distinctness conditions on the first chord's endpoints). -/
theorem ChordSep.swap_all {N : ℕ} [NeZero N] (X Y Z : Chord N)
    (h1 : X.1 ≠ Y.1) (h2 : X.1 ≠ Y.2) (h3 : X.1 ≠ Z.1) (h4 : X.1 ≠ Z.2)
    (h5 : X.2 ≠ Y.1) (h6 : X.2 ≠ Y.2) (h7 : X.2 ≠ Z.1) (h8 : X.2 ≠ Z.2) :
    ChordSep (X.2, X.1) (Y.2, Y.1) (Z.2, Z.1) ↔ ChordSep X Y Z := by
  by_cases hXX : X.1 = X.2
  · -- degenerate first chord: both sides are false since every atom is irreflexive
    rw [hXX]
    unfold ChordSep
    constructor
    · rintro (⟨g1, -, -, -⟩ | ⟨-, -, g3, -⟩)
      · exact absurd g1 sbtw_irrefl_left_right
      · exact absurd g3 sbtw_irrefl_left_right
    · rintro (⟨g1, -, -, -⟩ | ⟨-, -, g3, -⟩)
      · rw [hXX] at g1
        exact absurd g1 sbtw_irrefl_left_right
      · rw [hXX] at g3
        exact absurd g3 sbtw_irrefl_left_right
  · have key : ∀ w : ZMod N, X.1 ≠ w → X.2 ≠ w → (sbtw X.2 w X.1 ↔ ¬ sbtw X.1 w X.2) := by
      intro w hw1 hw2
      exact sbtw_not_reverse hw2 hw1.symm hXX
    unfold ChordSep
    show ((sbtw X.2 Y.2 X.1 ∧ sbtw X.2 Y.1 X.1 ∧ ¬ sbtw X.2 Z.2 X.1 ∧ ¬ sbtw X.2 Z.1 X.1) ∨
        (¬ sbtw X.2 Y.2 X.1 ∧ ¬ sbtw X.2 Y.1 X.1 ∧ sbtw X.2 Z.2 X.1 ∧ sbtw X.2 Z.1 X.1)) ↔
      ((sbtw X.1 Y.1 X.2 ∧ sbtw X.1 Y.2 X.2 ∧ ¬ sbtw X.1 Z.1 X.2 ∧ ¬ sbtw X.1 Z.2 X.2) ∨
        (¬ sbtw X.1 Y.1 X.2 ∧ ¬ sbtw X.1 Y.2 X.2 ∧ sbtw X.1 Z.1 X.2 ∧ sbtw X.1 Z.2 X.2))
    rw [key Y.2 h2 h6, key Y.1 h1 h5, key Z.2 h4 h8, key Z.1 h3 h7]
    constructor
    · rintro (⟨g1, g2, g3, g4⟩ | ⟨g1, g2, g3, g4⟩)
      · exact Or.inr ⟨g2, g1, not_not.mp g4, not_not.mp g3⟩
      · exact Or.inl ⟨not_not.mp g2, not_not.mp g1, g4, g3⟩
    · rintro (⟨g1, g2, g3, g4⟩ | ⟨g1, g2, g3, g4⟩)
      · exact Or.inr ⟨not_not.mpr g2, not_not.mpr g1, g4, g3⟩
      · exact Or.inl ⟨g2, g1, not_not.mpr g4, not_not.mpr g3⟩

/-- Points with positive `θ` are different from the base point. -/
theorem ne_q₀_of_theta_pos {N : ℕ} [NeZero N] {q₀ x : ZMod N} (h : 0 < (x - q₀).val) :
    x ≠ q₀ := by
  intro he
  rw [he, sub_self, ZMod.val_zero] at h
  exact lt_irrefl _ h

/-- Points with ordered `θ`s are different. -/
theorem ne_of_theta_lt {N : ℕ} [NeZero N] {q₀ x y : ZMod N} (h : (x - q₀).val < (y - q₀).val) :
    x ≠ y := by
  intro he
  rw [he] at h
  exact lt_irrefl _ h

/-- If `p` is outside the open arc spanned by the endpoints of `X` (measured from
`q₀`), then `p` lies on the same side of `X` as every other outside point: the sign
`sbtw X.1 p X.2` depends only on the order of the endpoints of `X`. -/
theorem sbtw_out_iff {N : ℕ} [NeZero N] {q₀ : ZMod N} (X : Chord N) (p : ZMod N)
    (h1 : 0 < (X.1 - q₀).val) (h2 : 0 < (X.2 - q₀).val)
    (hp : (p - q₀).val = 0 ∨ ((p - q₀).val < (X.1 - q₀).val ∧ (p - q₀).val < (X.2 - q₀).val) ∨
      ((X.1 - q₀).val < (p - q₀).val ∧ (X.2 - q₀).val < (p - q₀).val)) :
    sbtw X.1 p X.2 ↔ (X.2 - q₀).val < (X.1 - q₀).val := by
  by_cases hXX : X.1 = X.2
  · rw [hXX]
    exact ⟨fun h => absurd h sbtw_irrefl_left_right, fun h => absurd h (lt_irrefl _)⟩
  · have hX1q0 : X.1 ≠ q₀ := ne_q₀_of_theta_pos h1
    have hX2q0 : X.2 ≠ q₀ := ne_q₀_of_theta_pos h2
    rcases hp with hp | ⟨hp1, hp2⟩ | ⟨hp1, hp2⟩
    · have hpq : p = q₀ := theta_inj (by rw [hp, sub_self, ZMod.val_zero])
      rw [hpq]
      exact sbtw_mid_q₀ hX1q0 hX2q0 hXX
    · by_cases hp0 : p = q₀
      · rw [hp0]
        exact sbtw_mid_q₀ hX1q0 hX2q0 hXX
      · have hX1p : X.1 ≠ p := fun he => by rw [he] at hp1; exact lt_irrefl _ hp1
        have hpX2 : p ≠ X.2 := fun he => by rw [he] at hp2; exact lt_irrefl _ hp2
        rw [sbtw_theta hX1q0 hp0 hX2q0 hX1p hpX2 (fun h => hXX h.symm)]
        constructor
        · rintro (⟨i1, i2⟩ | ⟨i1, i2⟩ | ⟨i1, i2⟩)
          · omega
          · exact i2
          · omega
        · intro h
          exact Or.inr (Or.inl ⟨by omega, h⟩)
    · by_cases hp0 : p = q₀
      · rw [hp0]
        exact sbtw_mid_q₀ hX1q0 hX2q0 hXX
      · have hX1p : X.1 ≠ p := fun he => by rw [he] at hp1; exact lt_irrefl _ hp1
        have hpX2 : p ≠ X.2 := fun he => by rw [he] at hp2; exact lt_irrefl _ hp2
        rw [sbtw_theta hX1q0 hp0 hX2q0 hX1p hpX2 (fun h => hXX h.symm)]
        constructor
        · rintro (⟨i1, i2⟩ | ⟨i1, i2⟩ | ⟨i1, i2⟩)
          · omega
          · omega
          · exact i1
        · intro h
          exact Or.inr (Or.inr ⟨h, by omega⟩)


/-- The `t < N - 1` case of the Claim's inductive step: the chord `T = {0, t}`
forces the point labelled `t` onto the other arc, and the `(N-1)`-chord
`E = {t, N-1-t}` is then non-aligned with `A, B` while avoiding the top label,
contradicting `aligned_step_del`. -/
theorem aligned_step_DE_lt {N : ℕ} [NeZero N] [NeZero (N - 1)] {σ : ZMod N ≃ ZMod N}
    (hN : 4 ≤ N) (hσ : Beautiful σ)
    (ih : ∀ M < N, ∀ [NeZero M], ∀ σ' : ZMod M ≃ ZMod M, Beautiful σ' →
      ∀ k : ℕ, ChordAligned (kChords σ' k))
    {A B C : Chord N} (hA : A ∈ kChords σ (N - 1)) (hB : B ∈ kChords σ (N - 1))
    (_hC : C ∈ kChords σ (N - 1)) (hAB : A ≠ B) (_hBC : B ≠ C) (_hAC : A ≠ C)
    (hC0 : C.1 = σ 0) (hC1 : C.2 = σ topLabelN)
    {q₀ q₁ fPos lPos : ZMod N} (hqq : q₀ ≠ q₁)
    (hq0 : q₀ = σ 0 ∨ q₀ = σ topLabelN) (hq1 : q₁ = σ 0 ∨ q₁ = σ topLabelN)
    (hside : ∀ x : ZMod N, x = A.1 ∨ x = A.2 ∨ x = B.1 ∨ x = B.2 → sbtw q₀ x q₁)
    (hfmem : sbtw q₀ fPos q₁) (hlmem : sbtw q₀ lPos q₁)
    (hfmin : ∀ x : ZMod N, sbtw q₀ x q₁ → (fPos - q₀).val ≤ (x - q₀).val)
    (hlmax : ∀ x : ZMod N, sbtw q₀ x q₁ → (x - q₀).val ≤ (lPos - q₀).val)
    (hfl : (fPos - q₀).val < (lPos - q₀).val)
    (ht : (σ.symm fPos).val + (σ.symm lPos).val < N - 1)
    (hnal : ¬ (ChordSep A B C ∨ ChordSep B A C ∨ ChordSep C A B)) : False := by
  rw [not_or, not_or] at hnal
  obtain ⟨hnal1, hnal2, hnal3⟩ := hnal
  -- theta bounds for the six points
  have hA1s := hside A.1 (Or.inl rfl)
  have hA2s := hside A.2 (Or.inr (Or.inl rfl))
  have hB1s := hside B.1 (Or.inr (Or.inr (Or.inl rfl)))
  have hB2s := hside B.2 (Or.inr (Or.inr (Or.inr rfl)))
  obtain ⟨hA1θ0, hA1θ1⟩ := theta_mem hA1s
  obtain ⟨hA2θ0, hA2θ1⟩ := theta_mem hA2s
  obtain ⟨hB1θ0, hB1θ1⟩ := theta_mem hB1s
  obtain ⟨hB2θ0, hB2θ1⟩ := theta_mem hB2s
  obtain ⟨hfθ0, hfθ1⟩ := theta_mem hfmem
  obtain ⟨hlθ0, hlθ1⟩ := theta_mem hlmem
  -- distinctness facts
  have hfq0 : fPos ≠ q₀ := ne_q₀_of_theta_pos hfθ0
  have hlq0 : lPos ≠ q₀ := ne_q₀_of_theta_pos hlθ0
  have hfq1 : fPos ≠ q₁ := ne_of_theta_lt hfθ1
  have hlq1 : lPos ≠ q₁ := ne_of_theta_lt hlθ1
  have hflne : fPos ≠ lPos := ne_of_theta_lt hfl
  have hq1q0 : q₁ ≠ q₀ := hqq.symm
  have hA1q0 : A.1 ≠ q₀ := ne_q₀_of_theta_pos hA1θ0
  have hA2q0 : A.2 ≠ q₀ := ne_q₀_of_theta_pos hA2θ0
  have hB1q0 : B.1 ≠ q₀ := ne_q₀_of_theta_pos hB1θ0
  have hB2q0 : B.2 ≠ q₀ := ne_q₀_of_theta_pos hB2θ0
  have hA1q1 : A.1 ≠ q₁ := ne_of_theta_lt hA1θ1
  have hA2q1 : A.2 ≠ q₁ := ne_of_theta_lt hA2θ1
  have hB1q1 : B.1 ≠ q₁ := ne_of_theta_lt hB1θ1
  have hB2q1 : B.2 ≠ q₁ := ne_of_theta_lt hB2θ1
  -- the endpoints of C are exactly q₀, q₁ in some order
  have hqcases : (q₀ = σ 0 ∧ q₁ = σ topLabelN) ∨ (q₀ = σ topLabelN ∧ q₁ = σ 0) := by
    rcases hq0 with h0 | h0 <;> rcases hq1 with h1 | h1
    · exact absurd (h0.trans h1.symm) hqq
    · exact Or.inl ⟨h0, h1⟩
    · exact Or.inr ⟨h0, h1⟩
    · exact absurd (h0.trans h1.symm) hqq
  -- labels f, l
  set f := σ.symm fPos with hfdef
  set l := σ.symm lPos with hldef
  have hfPos : σ f = fPos := Equiv.apply_symm_apply σ fPos
  have hlPos : σ l = lPos := Equiv.apply_symm_apply σ lPos
  have hf0 : f ≠ 0 := by
    intro he
    have h2 := congrArg σ he
    rw [hfPos] at h2
    rcases hqcases with ⟨g0, g1⟩ | ⟨g0, g1⟩
    · rw [h2, g0] at hfq0
      exact hfq0 rfl
    · rw [h2, g1] at hfq1
      exact hfq1 rfl
  have hftop : f ≠ topLabelN := by
    intro he
    have h2 := congrArg σ he
    rw [hfPos] at h2
    rcases hqcases with ⟨g0, g1⟩ | ⟨g0, g1⟩
    · rw [h2, g1] at hfq1
      exact hfq1 rfl
    · rw [h2, g0] at hfq0
      exact hfq0 rfl
  have hl0 : l ≠ 0 := by
    intro he
    have h2 := congrArg σ he
    rw [hlPos] at h2
    rcases hqcases with ⟨g0, g1⟩ | ⟨g0, g1⟩
    · rw [h2, g0] at hlq0
      exact hlq0 rfl
    · rw [h2, g1] at hlq1
      exact hlq1 rfl
  have hltop : l ≠ topLabelN := by
    intro he
    have h2 := congrArg σ he
    rw [hlPos] at h2
    rcases hqcases with ⟨g0, g1⟩ | ⟨g0, g1⟩
    · rw [h2, g1] at hlq1
      exact hlq1 rfl
    · rw [h2, g0] at hlq0
      exact hlq0 rfl
  have hfv0 : f.val ≠ 0 := fun h => hf0 (ZMod.val_injective _ (h.trans ZMod.val_zero.symm))
  have hlv0 : l.val ≠ 0 := fun h => hl0 (ZMod.val_injective _ (h.trans ZMod.val_zero.symm))
  have hfv1 : f.val ≠ N - 1 := fun h => hftop (ZMod.val_injective _ (h.trans topLabelN_val.symm))
  have hlv1 : l.val ≠ N - 1 := fun h => hltop (ZMod.val_injective _ (h.trans topLabelN_val.symm))
  have hfvpos : 1 ≤ f.val := by omega
  have hlvpos : 1 ≤ l.val := by omega
  have hfvlt := ZMod.val_lt f
  have hlvlt := ZMod.val_lt l
  -- the sum t and its properties
  set t := f.val + l.val with htdef
  have ht2 : 2 ≤ t := by omega
  have htN : t ≤ N - 2 := by omega
  set tb := ((t : ℕ) : ZMod N) with htbdef
  have htv : tb.val = t := by
    rw [htbdef, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega : t < N)]
  have ht0 : tb ≠ 0 := by
    intro he
    have h1 : tb.val = (0 : ZMod N).val := by rw [he]
    rw [htv, ZMod.val_zero] at h1
    omega
  have httop : tb ≠ topLabelN := by
    intro he
    have h1 : tb.val = (topLabelN : ZMod N).val := by rw [he]
    rw [htv, topLabelN_val] at h1
    omega
  have htPos0 : σ tb ≠ σ 0 := fun h => ht0 (σ.injective h)
  have htPostop : σ tb ≠ σ topLabelN := fun h => httop (σ.injective h)
  have htPosq0 : σ tb ≠ q₀ := by
    rcases hq0 with h | h <;> rw [h]
    · exact htPos0
    · exact htPostop
  have htPosq1 : σ tb ≠ q₁ := by
    rcases hq1 with h | h <;> rw [h]
    · exact htPos0
    · exact htPostop
  have htf : tb ≠ f := by
    intro he
    have h1 : tb.val = f.val := by rw [he]
    rw [htv] at h1
    omega
  have htl : tb ≠ l := by
    intro he
    have h1 : tb.val = l.val := by rw [he]
    rw [htv] at h1
    omega
  have htPosf : σ tb ≠ fPos := by
    rw [← hfPos]
    exact fun h => htf (σ.injective h)
  have htPosl : σ tb ≠ lPos := by
    rw [← hlPos]
    exact fun h => htl (σ.injective h)
  -- non-crossing of the t-chords {0, t} and {f, l}
  have hncTD : sbtw (σ 0) fPos (σ tb) ↔ sbtw (σ 0) lPos (σ tb) := by
    have hflne' : f ≠ l := by
      intro he
      apply hflne
      rw [← hfPos, ← hlPos, he]
    have hflnev : f.val ≠ l.val := fun h => hflne' (ZMod.val_injective _ h)
    rcases lt_or_gt_of_ne hflnev with hcase | hcase
    · have h4 := Beautiful.nonCross_four hσ (w := (0 : ZMod N)) (x := f) (y := l) (z := tb)
        (by rw [ZMod.val_zero]; omega) hcase
        (by rw [htv]; omega)
        (by rw [ZMod.val_zero, htv]; omega)
      rw [hfPos, hlPos] at h4
      exact h4.1
    · have h4 := Beautiful.nonCross_four hσ (w := (0 : ZMod N)) (x := l) (y := f) (z := tb)
        (by rw [ZMod.val_zero]; omega) hcase
        (by rw [htv]; omega)
        (by rw [ZMod.val_zero, htv]; omega)
      rw [hfPos, hlPos] at h4
      exact h4.1.symm
  -- the position of t is strictly on the far arc of D = {fPos, lPos}
  have htPos : sbtw lPos (σ tb) fPos := by
    by_contra hcon
    have h1 : sbtw fPos (σ tb) lPos := by
      by_contra h2
      exact hcon ((sbtw_not_reverse htPosl.symm htPosf hflne).mpr h2)
    have htθ : (fPos - q₀).val < (σ tb - q₀).val ∧ (σ tb - q₀).val < (lPos - q₀).val := by
      have hs := (sbtw_theta hfq0 htPosq0 hlq0 htPosf.symm htPosl hflne.symm).mp h1
      rcases hs with ⟨g1, g2⟩ | ⟨g1, g2⟩ | ⟨g1, g2⟩
      · exact ⟨g1, g2⟩
      · omega
      · omega
    rcases hqcases with ⟨g0, g1⟩ | ⟨g0, g1⟩
    · have gA : sbtw (σ 0) fPos (σ tb) := by
        rw [← g0]
        exact (sbtw_val hfq0.symm).mpr htθ.1
      have gB : ¬ sbtw (σ 0) lPos (σ tb) := by
        rw [← g0, sbtw_val hlq0.symm]
        omega
      exact gB (hncTD.mp gA)
    · have gA : sbtw (σ 0) fPos (σ tb) := by
        rw [← g1]
        rw [sbtw_theta hq1q0 hfq0 htPosq0 hfq1.symm htPosf.symm htPosq1]
        exact Or.inr (Or.inl ⟨htθ.1, htθ.2.trans hlθ1⟩)
      have gB : ¬ sbtw (σ 0) lPos (σ tb) := by
        rw [← g1, sbtw_theta hq1q0 hlq0 htPosq0 hlq1.symm htPosl.symm htPosq1]
        rintro (⟨i1, i2⟩ | ⟨i1, i2⟩ | ⟨i1, i2⟩)
        · omega
        · omega
        · omega
      exact gB (hncTD.mp gA)
  -- nothing is strictly before fPos / strictly after lPos
  have hF4 : ∀ y : ZMod N, ¬ sbtw q₀ y fPos := by
    intro y hy
    have hq0y : q₀ ≠ y := by
      intro he
      rw [he] at hy
      exact sbtw_irrefl_left hy
    have hyθ : (y - q₀).val < (fPos - q₀).val := (sbtw_val hq0y).mp hy
    have hyme : sbtw q₀ y q₁ := (sbtw_val hq0y).mpr (hyθ.trans hfθ1)
    have := hfmin y hyme
    omega
  have hF5 : ∀ y : ZMod N, ¬ sbtw lPos y q₁ := by
    intro y hy
    have hyq1 : y ≠ q₁ := by
      intro he
      rw [he] at hy
      exact sbtw_irrefl_right hy
    have hyq0 : y ≠ q₀ := by
      intro he
      rw [he] at hy
      have := (sbtw_mid_q₀ hlq0 hq1q0 hlq1).mp hy
      omega
    have hly : lPos ≠ y := by
      intro he
      rw [he] at hy
      exact sbtw_irrefl_left hy
    have hs := (sbtw_theta hlq0 hyq0 hq1q0 hly hyq1 hlq1.symm).mp hy
    rcases hs with ⟨g1, g2⟩ | ⟨g1, g2⟩ | ⟨g1, g2⟩
    · have hyme : sbtw q₀ y q₁ := (sbtw_val hyq0.symm).mpr (by omega : (y - q₀).val < (q₁ - q₀).val)
      have := hlmax y hyme
      omega
    · omega
    · omega
  -- t lies on the other arc of C
  have htPosOther : sbtw q₁ (σ tb) q₀ := by
    have hs := (sbtw_theta hlq0 htPosq0 hfq0 htPosl.symm htPosf hflne).mp htPos
    rcases hs with ⟨g1, g2⟩ | ⟨g1, g2⟩ | ⟨g1, g2⟩
    · omega
    · have g : sbtw q₀ (σ tb) fPos := (sbtw_val htPosq0.symm).mpr g1
      exact absurd g (hF4 _)
    · by_cases hcase : (σ tb - q₀).val < (q₁ - q₀).val
      · have g : sbtw lPos (σ tb) q₁ :=
          (sbtw_theta hlq0 htPosq0 hq1q0 htPosl.symm htPosq1 hlq1.symm).mpr (Or.inl ⟨g2, hcase⟩)
        exact absurd g (hF5 _)
      · by_cases hcase2 : (σ tb - q₀).val = (q₁ - q₀).val
        · exact absurd (theta_inj hcase2) htPosq1
        · have g : (q₁ - q₀).val < (σ tb - q₀).val := by omega
          exact (sbtw_last_q₀ hq1q0 htPosq0 htPosq1.symm).mpr g
  have htθ' : (q₁ - q₀).val < (σ tb - q₀).val :=
    (sbtw_last_q₀ hq1q0 htPosq0 htPosq1.symm).mp htPosOther
  -- the complementary label N-1-t
  set t' := (((N - 1 - t : ℕ)) : ZMod N) with ht'def
  have ht'v : t'.val = N - 1 - t := by
    rw [ht'def, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega : N - 1 - t < N)]
  have ht'0 : t' ≠ 0 := by
    intro he
    have h1 : t'.val = (0 : ZMod N).val := by rw [he]
    rw [ht'v, ZMod.val_zero] at h1
    omega
  have ht'top : t' ≠ topLabelN := by
    intro he
    have h1 : t'.val = (topLabelN : ZMod N).val := by rw [he]
    rw [ht'v, topLabelN_val] at h1
    omega
  have ht'Pos0 : σ t' ≠ σ 0 := fun h => ht'0 (σ.injective h)
  have ht'Postop : σ t' ≠ σ topLabelN := fun h => ht'top (σ.injective h)
  have ht'q0 : σ t' ≠ q₀ := by
    rcases hq0 with h | h <;> rw [h]
    · exact ht'Pos0
    · exact ht'Postop
  have ht'q1 : σ t' ≠ q₁ := by
    rcases hq1 with h | h <;> rw [h]
    · exact ht'Pos0
    · exact ht'Postop
  have htop0 : σ 0 ≠ σ topLabelN := by
    intro h
    have h1 : (0 : ZMod N) = topLabelN := σ.injective h
    have h2 : (0 : ZMod N).val = (topLabelN : ZMod N).val := by rw [h1]
    rw [ZMod.val_zero, topLabelN_val] at h2
    omega
  -- non-crossing of the (N-1)-chords C and {t, N-1-t}
  have hncCE : sbtw (σ 0) (σ tb) (σ topLabelN) ↔ sbtw (σ 0) (σ t') (σ topLabelN) := by
    by_cases htt' : tb = t'
    · rw [← htt']
    · have hne : tb.val ≠ t'.val := fun h => htt' (ZMod.val_injective _ h)
      rcases lt_or_gt_of_ne hne with hcase | hcase
      · exact (Beautiful.nonCross_four hσ (w := (0 : ZMod N)) (x := tb) (y := t') (z := topLabelN)
          (by rw [ZMod.val_zero, htv]; omega) hcase
          (by rw [ht'v, topLabelN_val]; omega)
          (by rw [ZMod.val_zero, topLabelN_val, htv, ht'v]; omega)).1
      · exact ((Beautiful.nonCross_four hσ (w := (0 : ZMod N)) (x := t') (y := tb) (z := topLabelN)
          (by rw [ZMod.val_zero, ht'v]; omega) hcase
          (by rw [htv, topLabelN_val]; omega)
          (by rw [ZMod.val_zero, topLabelN_val, htv, ht'v]; omega)).1).symm
  -- N-1-t lies on the other arc as well
  have hntPosOther : sbtw q₁ (σ t') q₀ := by
    rcases hqcases with ⟨g0, g1⟩ | ⟨g0, g1⟩
    · have gA : ¬ sbtw (σ 0) (σ tb) (σ topLabelN) := by
        have h := htPosOther
        rw [g0, g1] at h
        exact (sbtw_not_reverse htPostop.symm htPos0 htop0).mp h
      have gB : ¬ sbtw (σ 0) (σ t') (σ topLabelN) := fun h => gA (hncCE.mpr h)
      have gC : sbtw (σ topLabelN) (σ t') (σ 0) :=
        (sbtw_not_reverse ht'Postop.symm ht'Pos0 htop0).mpr gB
      rw [← g0, ← g1] at gC
      exact gC
    · have gA : sbtw (σ 0) (σ tb) (σ topLabelN) := by
        have h := htPosOther
        rwa [g0, g1] at h
      have gB : sbtw (σ 0) (σ t') (σ topLabelN) := hncCE.mp gA
      rwa [← g0, ← g1] at gB
  have hntθ' : (q₁ - q₀).val < (σ t' - q₀).val :=
    (sbtw_last_q₀ hq1q0 ht'q0 ht'q1.symm).mp hntPosOther
  -- the chord E, ordered by label value
  set E' : Chord N := if tb.val ≤ t'.val then (σ tb, σ t') else (σ t', σ tb) with hE'def
  have hE'mem : E' ∈ kChords σ (N - 1) := by
    rw [hE'def]
    by_cases hle : tb.val ≤ t'.val
    · rw [if_pos hle, mem_kChords]
      exact ⟨tb, t', by rw [htv, ht'v]; omega, hle, rfl⟩
    · rw [if_neg hle, mem_kChords]
      exact ⟨t', tb, by rw [htv, ht'v]; omega, by omega, rfl⟩
  have hE'1 : E'.1 = σ tb ∨ E'.1 = σ t' := by
    rw [hE'def]
    by_cases hle : tb.val ≤ t'.val
    · rw [if_pos hle]
      exact Or.inl rfl
    · rw [if_neg hle]
      exact Or.inr rfl
  have hE'2 : E'.2 = σ tb ∨ E'.2 = σ t' := by
    rw [hE'def]
    by_cases hle : tb.val ≤ t'.val
    · rw [if_pos hle]
      exact Or.inr rfl
    · rw [if_neg hle]
      exact Or.inl rfl
  have hE'2top : E'.2 ≠ σ topLabelN := by
    rcases hE'2 with h | h <;> rw [h]
    · exact fun he => httop (σ.injective he)
    · exact fun he => ht'top (σ.injective he)
  have hE'1θ : (q₁ - q₀).val < (E'.1 - q₀).val := by
    rcases hE'1 with h | h <;> rw [h]
    · exact htθ'
    · exact hntθ'
  have hE'2θ : (q₁ - q₀).val < (E'.2 - q₀).val := by
    rcases hE'2 with h | h <;> rw [h]
    · exact htθ'
    · exact hntθ'
  have hAE' : A ≠ E' := by
    intro he
    have g1 := hA1θ1
    rw [he] at g1
    omega
  have hBE' : B ≠ E' := by
    intro he
    have g1 := hB1θ1
    rw [he] at g1
    omega
  -- separation equivalences
  have hp_of_far : ∀ (X : Chord N), (X.1 - q₀).val < (q₁ - q₀).val →
      (X.2 - q₀).val < (q₁ - q₀).val → ∀ p : ZMod N,
      (p = q₀ ∨ p = q₁ ∨ (q₁ - q₀).val < (p - q₀).val) →
      (p - q₀).val = 0 ∨ ((p - q₀).val < (X.1 - q₀).val ∧ (p - q₀).val < (X.2 - q₀).val) ∨
        ((X.1 - q₀).val < (p - q₀).val ∧ (X.2 - q₀).val < (p - q₀).val) := by
    intro X hX1θ1 hX2θ1 p hp
    rcases hp with rfl | rfl | hp
    · exact Or.inl (by rw [sub_self, ZMod.val_zero])
    · exact Or.inr (Or.inr ⟨hX1θ1, hX2θ1⟩)
    · exact Or.inr (Or.inr ⟨by omega, by omega⟩)
  have hC1far : C.1 = q₀ ∨ C.1 = q₁ ∨ (q₁ - q₀).val < (C.1 - q₀).val := by
    rw [hC0]
    rcases hqcases with ⟨g0, g1⟩ | ⟨g0, g1⟩
    · exact Or.inl g0.symm
    · exact Or.inr (Or.inl g1.symm)
  have hC2far : C.2 = q₀ ∨ C.2 = q₁ ∨ (q₁ - q₀).val < (C.2 - q₀).val := by
    rw [hC1]
    rcases hqcases with ⟨g0, g1⟩ | ⟨g0, g1⟩
    · exact Or.inr (Or.inl g1.symm)
    · exact Or.inl g0.symm
  have hE'1far : E'.1 = q₀ ∨ E'.1 = q₁ ∨ (q₁ - q₀).val < (E'.1 - q₀).val :=
    Or.inr (Or.inr hE'1θ)
  have hE'2far : E'.2 = q₀ ∨ E'.2 = q₁ ∨ (q₁ - q₀).val < (E'.2 - q₀).val :=
    Or.inr (Or.inr hE'2θ)
  have eA : ChordSep A B C ↔ ChordSep A B E' := by
    unfold ChordSep
    rw [sbtw_out_iff A C.1 hA1θ0 hA2θ0 (hp_of_far A hA1θ1 hA2θ1 C.1 hC1far),
      sbtw_out_iff A C.2 hA1θ0 hA2θ0 (hp_of_far A hA1θ1 hA2θ1 C.2 hC2far),
      sbtw_out_iff A E'.1 hA1θ0 hA2θ0 (hp_of_far A hA1θ1 hA2θ1 E'.1 hE'1far),
      sbtw_out_iff A E'.2 hA1θ0 hA2θ0 (hp_of_far A hA1θ1 hA2θ1 E'.2 hE'2far)]
  have eB : ChordSep B A C ↔ ChordSep B A E' := by
    unfold ChordSep
    rw [sbtw_out_iff B C.1 hB1θ0 hB2θ0 (hp_of_far B hB1θ1 hB2θ1 C.1 hC1far),
      sbtw_out_iff B C.2 hB1θ0 hB2θ0 (hp_of_far B hB1θ1 hB2θ1 C.2 hC2far),
      sbtw_out_iff B E'.1 hB1θ0 hB2θ0 (hp_of_far B hB1θ1 hB2θ1 E'.1 hE'1far),
      sbtw_out_iff B E'.2 hB1θ0 hB2θ0 (hp_of_far B hB1θ1 hB2θ1 E'.2 hE'2far)]
  have hnsE : ¬ ChordSep E' A B := by
    have hE'1q0 : E'.1 ≠ q₀ := ne_q₀_of_theta_pos (by omega : 0 < (E'.1 - q₀).val)
    have hE'2q0 : E'.2 ≠ q₀ := ne_q₀_of_theta_pos (by omega : 0 < (E'.2 - q₀).val)
    by_cases hEE : E'.1 = E'.2
    · intro h
      unfold ChordSep at h
      rw [hEE] at h
      rcases h with ⟨g1, -, -, -⟩ | ⟨-, -, g3, -⟩
      · exact absurd g1 sbtw_irrefl_left_right
      · exact absurd g3 sbtw_irrefl_left_right
    · have ekey : ∀ w : ZMod N, 0 < (w - q₀).val → (w - q₀).val < (q₁ - q₀).val →
          (sbtw E'.1 w E'.2 ↔ (E'.2 - q₀).val < (E'.1 - q₀).val) := by
        intro w hw0 hw1
        have hwq0 : w ≠ q₀ := ne_q₀_of_theta_pos hw0
        have hE'1w : E'.1 ≠ w := fun he => by rw [he] at hE'1θ; omega
        have hwE'2 : w ≠ E'.2 := fun he => by rw [he] at hw1; omega
        rw [sbtw_theta hE'1q0 hwq0 hE'2q0 hE'1w hwE'2 (fun h => hEE h.symm)]
        constructor
        · rintro (⟨i1, i2⟩ | ⟨i1, i2⟩ | ⟨i1, i2⟩)
          · omega
          · exact i2
          · omega
        · intro h
          exact Or.inr (Or.inl ⟨by omega, h⟩)
      unfold ChordSep
      rw [ekey A.1 hA1θ0 hA1θ1, ekey A.2 hA2θ0 hA2θ1, ekey B.1 hB1θ0 hB1θ1,
        ekey B.2 hB2θ0 hB2θ1]
      rintro (⟨g1, -, g3, -⟩ | ⟨g1, -, g3, -⟩)
      · exact g3 g1
      · exact g1 g3
  -- final application of the deletion lemma to A, B, E
  have hnotop : A.2 ≠ σ topLabelN ∧ B.2 ≠ σ topLabelN ∧ E'.2 ≠ σ topLabelN := by
    refine ⟨?_, ?_, hE'2top⟩
    · rcases hqcases with ⟨g0, g1⟩ | ⟨g0, g1⟩
      · rw [← g1]
        exact hA2q1
      · rw [← g0]
        exact hA2q0
    · rcases hqcases with ⟨g0, g1⟩ | ⟨g0, g1⟩
      · rw [← g1]
        exact hB2q1
      · rw [← g0]
        exact hB2q0
  have hnal' : ¬ (ChordSep A B E' ∨ ChordSep B A E' ∨ ChordSep E' A B) := by
    rw [not_or, not_or]
    exact ⟨fun h => hnal1 (eA.mpr h), fun h => hnal2 (eB.mpr h), hnsE⟩
  exact aligned_step_del hN hσ ih hA hB hE'mem hAB hBE' hAE' kChords_disjoint hnotop hnal'

/-- The `t = N - 1` case of the Claim's inductive step: the chord `D = {f, l}` is
itself an `(N-1)`-chord, and `A, B, D` are non-aligned while avoiding the top label,
contradicting `aligned_step_del`. (If `D` coincides with `A` or `B`, then `A` resp.
`B` separates `B` resp. `A` from `C` directly.) -/
theorem aligned_step_DE_eq {N : ℕ} [NeZero N] [NeZero (N - 1)] {σ : ZMod N ≃ ZMod N}
    (hN : 4 ≤ N) (hσ : Beautiful σ)
    (ih : ∀ M < N, ∀ [NeZero M], ∀ σ' : ZMod M ≃ ZMod M, Beautiful σ' →
      ∀ k : ℕ, ChordAligned (kChords σ' k))
    {A B C : Chord N} (hA : A ∈ kChords σ (N - 1)) (hB : B ∈ kChords σ (N - 1))
    (_hC : C ∈ kChords σ (N - 1)) (hAB : A ≠ B) (_hBC : B ≠ C) (_hAC : A ≠ C)
    (hC0 : C.1 = σ 0) (hC1 : C.2 = σ topLabelN)
    {q₀ q₁ fPos lPos : ZMod N} (hqq : q₀ ≠ q₁)
    (hq0 : q₀ = σ 0 ∨ q₀ = σ topLabelN) (hq1 : q₁ = σ 0 ∨ q₁ = σ topLabelN)
    (hside : ∀ x : ZMod N, x = A.1 ∨ x = A.2 ∨ x = B.1 ∨ x = B.2 → sbtw q₀ x q₁)
    (hfmem : sbtw q₀ fPos q₁) (hlmem : sbtw q₀ lPos q₁)
    (hfmin : ∀ x : ZMod N, sbtw q₀ x q₁ → (fPos - q₀).val ≤ (x - q₀).val)
    (hlmax : ∀ x : ZMod N, sbtw q₀ x q₁ → (x - q₀).val ≤ (lPos - q₀).val)
    (hfl : (fPos - q₀).val < (lPos - q₀).val)
    (ht : (σ.symm fPos).val + (σ.symm lPos).val = N - 1)
    (hnal : ¬ (ChordSep A B C ∨ ChordSep B A C ∨ ChordSep C A B)) : False := by
  rw [not_or, not_or] at hnal
  obtain ⟨hnal1, hnal2, hnal3⟩ := hnal
  -- theta bounds for the six points
  have hA1s := hside A.1 (Or.inl rfl)
  have hA2s := hside A.2 (Or.inr (Or.inl rfl))
  have hB1s := hside B.1 (Or.inr (Or.inr (Or.inl rfl)))
  have hB2s := hside B.2 (Or.inr (Or.inr (Or.inr rfl)))
  obtain ⟨hA1θ0, hA1θ1⟩ := theta_mem hA1s
  obtain ⟨hA2θ0, hA2θ1⟩ := theta_mem hA2s
  obtain ⟨hB1θ0, hB1θ1⟩ := theta_mem hB1s
  obtain ⟨hB2θ0, hB2θ1⟩ := theta_mem hB2s
  obtain ⟨hfθ0, hfθ1⟩ := theta_mem hfmem
  obtain ⟨hlθ0, hlθ1⟩ := theta_mem hlmem
  -- distinctness facts
  have hfq0 : fPos ≠ q₀ := ne_q₀_of_theta_pos hfθ0
  have hlq0 : lPos ≠ q₀ := ne_q₀_of_theta_pos hlθ0
  have hfq1 : fPos ≠ q₁ := ne_of_theta_lt hfθ1
  have hlq1 : lPos ≠ q₁ := ne_of_theta_lt hlθ1
  have hflne : fPos ≠ lPos := ne_of_theta_lt hfl
  have hq1q0 : q₁ ≠ q₀ := hqq.symm
  have hA1q0 : A.1 ≠ q₀ := ne_q₀_of_theta_pos hA1θ0
  have hA2q0 : A.2 ≠ q₀ := ne_q₀_of_theta_pos hA2θ0
  have hB1q0 : B.1 ≠ q₀ := ne_q₀_of_theta_pos hB1θ0
  have hB2q0 : B.2 ≠ q₀ := ne_q₀_of_theta_pos hB2θ0
  have hA1q1 : A.1 ≠ q₁ := ne_of_theta_lt hA1θ1
  have hA2q1 : A.2 ≠ q₁ := ne_of_theta_lt hA2θ1
  have hB1q1 : B.1 ≠ q₁ := ne_of_theta_lt hB1θ1
  have hB2q1 : B.2 ≠ q₁ := ne_of_theta_lt hB2θ1
  -- the endpoints of C are exactly q₀, q₁ in some order
  have hqcases : (q₀ = σ 0 ∧ q₁ = σ topLabelN) ∨ (q₀ = σ topLabelN ∧ q₁ = σ 0) := by
    rcases hq0 with h0 | h0 <;> rcases hq1 with h1 | h1
    · exact absurd (h0.trans h1.symm) hqq
    · exact Or.inl ⟨h0, h1⟩
    · exact Or.inr ⟨h0, h1⟩
    · exact absurd (h0.trans h1.symm) hqq
  -- labels f, l
  set f := σ.symm fPos with hfdef
  set l := σ.symm lPos with hldef
  have hfPos : σ f = fPos := Equiv.apply_symm_apply σ fPos
  have hlPos : σ l = lPos := Equiv.apply_symm_apply σ lPos
  have hf0 : f ≠ 0 := by
    intro he
    have h2 := congrArg σ he
    rw [hfPos] at h2
    rcases hqcases with ⟨g0, g1⟩ | ⟨g0, g1⟩
    · rw [h2, g0] at hfq0
      exact hfq0 rfl
    · rw [h2, g1] at hfq1
      exact hfq1 rfl
  have hftop : f ≠ topLabelN := by
    intro he
    have h2 := congrArg σ he
    rw [hfPos] at h2
    rcases hqcases with ⟨g0, g1⟩ | ⟨g0, g1⟩
    · rw [h2, g1] at hfq1
      exact hfq1 rfl
    · rw [h2, g0] at hfq0
      exact hfq0 rfl
  have hl0 : l ≠ 0 := by
    intro he
    have h2 := congrArg σ he
    rw [hlPos] at h2
    rcases hqcases with ⟨g0, g1⟩ | ⟨g0, g1⟩
    · rw [h2, g0] at hlq0
      exact hlq0 rfl
    · rw [h2, g1] at hlq1
      exact hlq1 rfl
  have hltop : l ≠ topLabelN := by
    intro he
    have h2 := congrArg σ he
    rw [hlPos] at h2
    rcases hqcases with ⟨g0, g1⟩ | ⟨g0, g1⟩
    · rw [h2, g1] at hlq1
      exact hlq1 rfl
    · rw [h2, g0] at hlq0
      exact hlq0 rfl
  have hfl' : f ≠ l := fun he => hflne (by rw [← hfPos, he, hlPos])
  -- the chord D, ordered by label value
  set D' : Chord N := if f.val ≤ l.val then (σ f, σ l) else (σ l, σ f) with hD'def
  have hD'mem : D' ∈ kChords σ (N - 1) := by
    rw [hD'def]
    by_cases hle : f.val ≤ l.val
    · rw [if_pos hle, mem_kChords]
      exact ⟨f, l, by omega, hle, rfl⟩
    · rw [if_neg hle, mem_kChords]
      exact ⟨l, f, by omega, by omega, rfl⟩
  have hD'12 : D'.1 ≠ D'.2 := by
    rw [hD'def]
    by_cases hle : f.val ≤ l.val
    · rw [if_pos hle]
      exact fun h => hfl' (σ.injective (show σ f = σ l from h))
    · rw [if_neg hle]
      exact fun h => hfl' ((σ.injective (show σ l = σ f from h)).symm)
  have hDfset : fPos = D'.1 ∨ fPos = D'.2 := by
    rw [hD'def]
    by_cases hle : f.val ≤ l.val
    · rw [if_pos hle]
      exact Or.inl hfPos.symm
    · rw [if_neg hle]
      exact Or.inr hfPos.symm
  have hDlset : lPos = D'.1 ∨ lPos = D'.2 := by
    rw [hD'def]
    by_cases hle : f.val ≤ l.val
    · rw [if_pos hle]
      exact Or.inr hlPos.symm
    · rw [if_neg hle]
      exact Or.inl hlPos.symm
  have hD'2top : D'.2 ≠ σ topLabelN := by
    rw [hD'def]
    by_cases hle : f.val ≤ l.val
    · rw [if_pos hle]
      exact fun he => hltop (σ.injective (show σ l = σ topLabelN from he))
    · rw [if_neg hle]
      exact fun he => hftop (σ.injective (show σ f = σ topLabelN from he))
  -- C-side position facts
  have hCnot : ∀ p : ZMod N, p = q₀ ∨ p = q₁ → ¬ sbtw fPos p lPos := by
    intro p hp
    rcases hp with rfl | rfl
    · rw [sbtw_mid_q₀ hfq0 hlq0 hflne]
      omega
    · rw [sbtw_theta hfq0 hq1q0 hlq0 hfq1 hlq1.symm hflne.symm]
      rintro (⟨i1, i2⟩ | ⟨i1, i2⟩ | ⟨i1, i2⟩)
      · omega
      · omega
      · omega
  have hCpos : ∀ p : ZMod N, p = q₀ ∨ p = q₁ → sbtw lPos p fPos := by
    intro p hp
    rcases hp with rfl | rfl
    · exact (sbtw_mid_q₀ hlq0 hfq0 hflne.symm).mpr hfl
    · rw [sbtw_theta hlq0 hq1q0 hfq0 hlq1 hfq1.symm hflne]
      exact Or.inr (Or.inr ⟨hfl, hlθ1⟩)
  have hC1q : C.1 = q₀ ∨ C.1 = q₁ := by
    rw [hC0]
    rcases hqcases with ⟨g0, g1⟩ | ⟨g0, g1⟩
    · exact Or.inl g0.symm
    · exact Or.inr g1.symm
  have hC2q : C.2 = q₀ ∨ C.2 = q₁ := by
    rw [hC1]
    rcases hqcases with ⟨g0, g1⟩ | ⟨g0, g1⟩
    · exact Or.inr g1.symm
    · exact Or.inl g0.symm
  -- three-way case split on whether D is new
  by_cases hDA : D' = A
  · -- D = A: then A separates B from C
    have hsep : ChordSep A B C := by
      obtain ⟨d1, d2, d3, d4⟩ := kChords_disjoint A hA B hB hAB
      have hAfset : fPos = A.1 ∨ fPos = A.2 := by
        rw [hDA] at hDfset
        exact hDfset
      have hAlset : lPos = A.1 ∨ lPos = A.2 := by
        rw [hDA] at hDlset
        exact hDlset
      have hwf : ∀ w : ZMod N, w = B.1 ∨ w = B.2 → w ≠ fPos := by
        intro w hw
        rcases hAfset with h | h
        · rw [h]
          rcases hw with rfl | rfl
          · exact d1.symm
          · exact d2.symm
        · rw [h]
          rcases hw with rfl | rfl
          · exact d3.symm
          · exact d4.symm
      have hwl : ∀ w : ZMod N, w = B.1 ∨ w = B.2 → w ≠ lPos := by
        intro w hw
        rcases hAlset with h | h
        · rw [h]
          rcases hw with rfl | rfl
          · exact d1.symm
          · exact d2.symm
        · rw [h]
          rcases hw with rfl | rfl
          · exact d3.symm
          · exact d4.symm
      have hBin : ∀ w : ZMod N, w = B.1 ∨ w = B.2 →
          (fPos - q₀).val < (w - q₀).val ∧ (w - q₀).val < (lPos - q₀).val := by
        intro w hw
        have hws := hside w (Or.inr (Or.inr hw))
        have hmin := hfmin w hws
        have hmax := hlmax w hws
        have h1 : (fPos - q₀).val ≠ (w - q₀).val := fun h => hwf w hw (theta_inj h).symm
        have h2 : (w - q₀).val ≠ (lPos - q₀).val := fun h => hwl w hw (theta_inj h)
        omega
      have hq0B1 : B.1 ≠ q₀ :=
        ne_q₀_of_theta_pos (by have := hBin B.1 (Or.inl rfl); omega : 0 < (B.1 - q₀).val)
      have hq0B2 : B.2 ≠ q₀ :=
        ne_q₀_of_theta_pos (by have := hBin B.2 (Or.inr rfl); omega : 0 < (B.2 - q₀).val)
      rcases hAfset with hA1f' | hA2f'
      · have hA1f : A.1 = fPos := hA1f'.symm
        have hA2l : A.2 = lPos := by
          rcases hAlset with h | h
          · exact absurd (hA1f'.trans h.symm) hflne
          · exact h.symm
        refine Or.inl ⟨?_, ?_, ?_, ?_⟩
        · rw [hA1f, hA2l]
          exact (sbtw_theta hfq0 hq0B1 hlq0 (hwf B.1 (Or.inl rfl)).symm
            (hwl B.1 (Or.inl rfl)) hflne.symm).mpr (Or.inl (hBin B.1 (Or.inl rfl)))
        · rw [hA1f, hA2l]
          exact (sbtw_theta hfq0 hq0B2 hlq0 (hwf B.2 (Or.inr rfl)).symm
            (hwl B.2 (Or.inr rfl)) hflne.symm).mpr (Or.inl (hBin B.2 (Or.inr rfl)))
        · rw [hA1f, hA2l]
          exact hCnot C.1 hC1q
        · rw [hA1f, hA2l]
          exact hCnot C.2 hC2q
      · have hA2f : A.2 = fPos := hA2f'.symm
        have hA1l : A.1 = lPos := by
          rcases hAlset with h | h
          · exact h.symm
          · exact absurd (hA2f'.trans h.symm) hflne
        refine Or.inr ⟨?_, ?_, ?_, ?_⟩
        · rw [hA1l, hA2f]
          have hb := hBin B.1 (Or.inl rfl)
          rw [sbtw_theta hlq0 hq0B1 hfq0 (hwl B.1 (Or.inl rfl)).symm (hwf B.1 (Or.inl rfl))
            hflne]
          rintro (⟨i1, i2⟩ | ⟨i1, i2⟩ | ⟨i1, i2⟩)
          · omega
          · omega
          · omega
        · rw [hA1l, hA2f]
          have hb := hBin B.2 (Or.inr rfl)
          rw [sbtw_theta hlq0 hq0B2 hfq0 (hwl B.2 (Or.inr rfl)).symm (hwf B.2 (Or.inr rfl))
            hflne]
          rintro (⟨i1, i2⟩ | ⟨i1, i2⟩ | ⟨i1, i2⟩)
          · omega
          · omega
          · omega
        · rw [hA1l, hA2f]
          exact hCpos C.1 hC1q
        · rw [hA1l, hA2f]
          exact hCpos C.2 hC2q
    exact hnal1 hsep
  · by_cases hDB : D' = B
    · -- D = B: then B separates A from C
      have hsep : ChordSep B A C := by
        obtain ⟨d1, d2, d3, d4⟩ := kChords_disjoint A hA B hB hAB
        have hBfset : fPos = B.1 ∨ fPos = B.2 := by
          rw [hDB] at hDfset
          exact hDfset
        have hBlset : lPos = B.1 ∨ lPos = B.2 := by
          rw [hDB] at hDlset
          exact hDlset
        have hwf : ∀ w : ZMod N, w = A.1 ∨ w = A.2 → w ≠ fPos := by
          intro w hw
          rcases hBfset with h | h
          · rw [h]
            rcases hw with rfl | rfl
            · exact d1
            · exact d3
          · rw [h]
            rcases hw with rfl | rfl
            · exact d2
            · exact d4
        have hwl : ∀ w : ZMod N, w = A.1 ∨ w = A.2 → w ≠ lPos := by
          intro w hw
          rcases hBlset with h | h
          · rw [h]
            rcases hw with rfl | rfl
            · exact d1
            · exact d3
          · rw [h]
            rcases hw with rfl | rfl
            · exact d2
            · exact d4
        have hAin : ∀ w : ZMod N, w = A.1 ∨ w = A.2 →
            (fPos - q₀).val < (w - q₀).val ∧ (w - q₀).val < (lPos - q₀).val := by
          intro w hw
          have hws := hside w (by
            rcases hw with rfl | rfl
            · exact Or.inl rfl
            · exact Or.inr (Or.inl rfl))
          have hmin := hfmin w hws
          have hmax := hlmax w hws
          have h1 : (fPos - q₀).val ≠ (w - q₀).val := fun h => hwf w hw (theta_inj h).symm
          have h2 : (w - q₀).val ≠ (lPos - q₀).val := fun h => hwl w hw (theta_inj h)
          omega
        have hq0A1 : A.1 ≠ q₀ :=
          ne_q₀_of_theta_pos (by have := hAin A.1 (Or.inl rfl); omega : 0 < (A.1 - q₀).val)
        have hq0A2 : A.2 ≠ q₀ :=
          ne_q₀_of_theta_pos (by have := hAin A.2 (Or.inr rfl); omega : 0 < (A.2 - q₀).val)
        rcases hBfset with hB1f' | hB2f'
        · have hB1f : B.1 = fPos := hB1f'.symm
          have hB2l : B.2 = lPos := by
            rcases hBlset with h | h
            · exact absurd (hB1f'.trans h.symm) hflne
            · exact h.symm
          refine Or.inl ⟨?_, ?_, ?_, ?_⟩
          · rw [hB1f, hB2l]
            exact (sbtw_theta hfq0 hq0A1 hlq0 (hwf A.1 (Or.inl rfl)).symm
              (hwl A.1 (Or.inl rfl)) hflne.symm).mpr (Or.inl (hAin A.1 (Or.inl rfl)))
          · rw [hB1f, hB2l]
            exact (sbtw_theta hfq0 hq0A2 hlq0 (hwf A.2 (Or.inr rfl)).symm
              (hwl A.2 (Or.inr rfl)) hflne.symm).mpr (Or.inl (hAin A.2 (Or.inr rfl)))
          · rw [hB1f, hB2l]
            exact hCnot C.1 hC1q
          · rw [hB1f, hB2l]
            exact hCnot C.2 hC2q
        · have hB2f : B.2 = fPos := hB2f'.symm
          have hB1l : B.1 = lPos := by
            rcases hBlset with h | h
            · exact h.symm
            · exact absurd (hB2f'.trans h.symm) hflne
          refine Or.inr ⟨?_, ?_, ?_, ?_⟩
          · rw [hB1l, hB2f]
            have hb := hAin A.1 (Or.inl rfl)
            rw [sbtw_theta hlq0 hq0A1 hfq0 (hwl A.1 (Or.inl rfl)).symm (hwf A.1 (Or.inl rfl))
              hflne]
            rintro (⟨i1, i2⟩ | ⟨i1, i2⟩ | ⟨i1, i2⟩)
            · omega
            · omega
            · omega
          · rw [hB1l, hB2f]
            have hb := hAin A.2 (Or.inr rfl)
            rw [sbtw_theta hlq0 hq0A2 hfq0 (hwl A.2 (Or.inr rfl)).symm (hwf A.2 (Or.inr rfl))
              hflne]
            rintro (⟨i1, i2⟩ | ⟨i1, i2⟩ | ⟨i1, i2⟩)
            · omega
            · omega
            · omega
          · rw [hB1l, hB2f]
            exact hCpos C.1 hC1q
          · rw [hB1l, hB2f]
            exact hCpos C.2 hC2q
      exact hnal2 hsep
    · -- D is fresh: A, B, D are non-aligned and avoid the top label
      obtain ⟨dAD1, dAD2, dAD3, dAD4⟩ := kChords_disjoint A hA D' hD'mem (fun h => hDA h.symm)
      obtain ⟨dBD1, dBD2, dBD3, dBD4⟩ := kChords_disjoint B hB D' hD'mem (fun h => hDB h.symm)
      have hAin : ∀ w : ZMod N, w = A.1 ∨ w = A.2 →
          (fPos - q₀).val < (w - q₀).val ∧ (w - q₀).val < (lPos - q₀).val := by
        intro w hw
        have hws := hside w (by
          rcases hw with rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr (Or.inl rfl))
        have hmin := hfmin w hws
        have hmax := hlmax w hws
        have hwf : w ≠ fPos := by
          rcases hDfset with h | h
          · rw [h]
            rcases hw with rfl | rfl
            · exact dAD1
            · exact dAD3
          · rw [h]
            rcases hw with rfl | rfl
            · exact dAD2
            · exact dAD4
        have hwl : w ≠ lPos := by
          rcases hDlset with h | h
          · rw [h]
            rcases hw with rfl | rfl
            · exact dAD1
            · exact dAD3
          · rw [h]
            rcases hw with rfl | rfl
            · exact dAD2
            · exact dAD4
        have h1 : (fPos - q₀).val ≠ (w - q₀).val := fun h => hwf (theta_inj h).symm
        have h2 : (w - q₀).val ≠ (lPos - q₀).val := fun h => hwl (theta_inj h)
        omega
      have hBin : ∀ w : ZMod N, w = B.1 ∨ w = B.2 →
          (fPos - q₀).val < (w - q₀).val ∧ (w - q₀).val < (lPos - q₀).val := by
        intro w hw
        have hws := hside w (Or.inr (Or.inr hw))
        have hmin := hfmin w hws
        have hmax := hlmax w hws
        have hwf : w ≠ fPos := by
          rcases hDfset with h | h
          · rw [h]
            rcases hw with rfl | rfl
            · exact dBD1
            · exact dBD3
          · rw [h]
            rcases hw with rfl | rfl
            · exact dBD2
            · exact dBD4
        have hwl : w ≠ lPos := by
          rcases hDlset with h | h
          · rw [h]
            rcases hw with rfl | rfl
            · exact dBD1
            · exact dBD3
          · rw [h]
            rcases hw with rfl | rfl
            · exact dBD2
            · exact dBD4
        have h1 : (fPos - q₀).val ≠ (w - q₀).val := fun h => hwf (theta_inj h).symm
        have h2 : (w - q₀).val ≠ (lPos - q₀).val := fun h => hwl (theta_inj h)
        omega
      -- separation equivalences
      have hpA_of : ∀ p : ZMod N, (p = q₀ ∨ p = q₁ ∨ p = fPos ∨ p = lPos) →
          (p - q₀).val = 0 ∨ ((p - q₀).val < (A.1 - q₀).val ∧ (p - q₀).val < (A.2 - q₀).val) ∨
            ((A.1 - q₀).val < (p - q₀).val ∧ (A.2 - q₀).val < (p - q₀).val) := by
        intro p hp
        obtain ⟨hA1in, hA2in⟩ := hAin A.1 (Or.inl rfl), hAin A.2 (Or.inr rfl)
        rcases hp with rfl | rfl | rfl | rfl
        · exact Or.inl (by rw [sub_self, ZMod.val_zero])
        · exact Or.inr (Or.inr ⟨hA1θ1, hA2θ1⟩)
        · exact Or.inr (Or.inl ⟨hA1in.1, hA2in.1⟩)
        · exact Or.inr (Or.inr ⟨hA1in.2, hA2in.2⟩)
      have hpB_of : ∀ p : ZMod N, (p = q₀ ∨ p = q₁ ∨ p = fPos ∨ p = lPos) →
          (p - q₀).val = 0 ∨ ((p - q₀).val < (B.1 - q₀).val ∧ (p - q₀).val < (B.2 - q₀).val) ∨
            ((B.1 - q₀).val < (p - q₀).val ∧ (B.2 - q₀).val < (p - q₀).val) := by
        intro p hp
        obtain ⟨hB1in, hB2in⟩ := hBin B.1 (Or.inl rfl), hBin B.2 (Or.inr rfl)
        rcases hp with rfl | rfl | rfl | rfl
        · exact Or.inl (by rw [sub_self, ZMod.val_zero])
        · exact Or.inr (Or.inr ⟨hB1θ1, hB2θ1⟩)
        · exact Or.inr (Or.inl ⟨hB1in.1, hB2in.1⟩)
        · exact Or.inr (Or.inr ⟨hB1in.2, hB2in.2⟩)
      have hC1far : C.1 = q₀ ∨ C.1 = q₁ ∨ C.1 = fPos ∨ C.1 = lPos := by
        rcases hC1q with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      have hC2far : C.2 = q₀ ∨ C.2 = q₁ ∨ C.2 = fPos ∨ C.2 = lPos := by
        rcases hC2q with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      have hD'1far : D'.1 = q₀ ∨ D'.1 = q₁ ∨ D'.1 = fPos ∨ D'.1 = lPos := by
        rcases hDfset with h | h
        · exact Or.inr (Or.inr (Or.inl h.symm))
        · rcases hDlset with h' | h'
          · exact Or.inr (Or.inr (Or.inr h'.symm))
          · exact absurd (h.trans h'.symm) hflne
      have hD'2far : D'.2 = q₀ ∨ D'.2 = q₁ ∨ D'.2 = fPos ∨ D'.2 = lPos := by
        rcases hDlset with h | h
        · rcases hDfset with h' | h'
          · exact absurd (h'.trans h.symm) hflne
          · exact Or.inr (Or.inr (Or.inl h'.symm))
        · exact Or.inr (Or.inr (Or.inr h.symm))
      have eA : ChordSep A B C ↔ ChordSep A B D' := by
        unfold ChordSep
        rw [sbtw_out_iff A C.1 hA1θ0 hA2θ0 (hpA_of C.1 hC1far),
          sbtw_out_iff A C.2 hA1θ0 hA2θ0 (hpA_of C.2 hC2far),
          sbtw_out_iff A D'.1 hA1θ0 hA2θ0 (hpA_of D'.1 hD'1far),
          sbtw_out_iff A D'.2 hA1θ0 hA2θ0 (hpA_of D'.2 hD'2far)]
      have eB : ChordSep B A C ↔ ChordSep B A D' := by
        unfold ChordSep
        rw [sbtw_out_iff B C.1 hB1θ0 hB2θ0 (hpB_of C.1 hC1far),
          sbtw_out_iff B C.2 hB1θ0 hB2θ0 (hpB_of C.2 hC2far),
          sbtw_out_iff B D'.1 hB1θ0 hB2θ0 (hpB_of D'.1 hD'1far),
          sbtw_out_iff B D'.2 hB1θ0 hB2θ0 (hpB_of D'.2 hD'2far)]
      -- D does not separate A from B
      have hnsD : ¬ ChordSep D' A B := by
        have hflf : ∀ w : ZMod N, w = A.1 ∨ w = A.2 ∨ w = B.1 ∨ w = B.2 →
            (fPos - q₀).val < (w - q₀).val ∧ (w - q₀).val < (lPos - q₀).val := by
          intro w hw
          rcases hw with h | h | h | h
          · exact hAin w (Or.inl h)
          · exact hAin w (Or.inr h)
          · exact hBin w (Or.inl h)
          · exact hBin w (Or.inr h)
        have hwf : ∀ w : ZMod N, w = A.1 ∨ w = A.2 ∨ w = B.1 ∨ w = B.2 → w ≠ fPos := by
          intro w hw
          have h1 := (hflf w hw).1
          intro he
          rw [he] at h1
          exact lt_irrefl _ h1
        have hwl : ∀ w : ZMod N, w = A.1 ∨ w = A.2 ∨ w = B.1 ∨ w = B.2 → w ≠ lPos := by
          intro w hw
          have h2 := (hflf w hw).2
          intro he
          rw [he] at h2
          exact lt_irrefl _ h2
        rcases hDfset with h1 | h1 <;> rcases hDlset with h2 | h2
        · exact absurd (h1.trans h2.symm) hflne
        · -- D' = (fPos, lPos): every atom sbtw fPos W lPos holds
          have ekey : ∀ w : ZMod N, w = A.1 ∨ w = A.2 ∨ w = B.1 ∨ w = B.2 →
              sbtw fPos w lPos := by
            intro w hw
            have hb := hflf w hw
            have hwq0 : w ≠ q₀ := ne_q₀_of_theta_pos (by omega : 0 < (w - q₀).val)
            exact (sbtw_theta hfq0 hwq0 hlq0 (hwf w hw).symm (hwl w hw) hflne.symm).mpr
              (Or.inl hb)
          have hDeq : D' = (fPos, lPos) := Prod.ext h1.symm h2.symm
          rw [hDeq]
          intro h
          rcases h with ⟨-, -, g3, -⟩ | ⟨g1, -, -, -⟩
          · exact g3 (ekey B.1 (Or.inr (Or.inr (Or.inl rfl))))
          · exact g1 (ekey A.1 (Or.inl rfl))
        · -- D' = (lPos, fPos): every atom sbtw lPos W fPos fails
          have ekey : ∀ w : ZMod N, w = A.1 ∨ w = A.2 ∨ w = B.1 ∨ w = B.2 →
              ¬ sbtw lPos w fPos := by
            intro w hw
            have hb := hflf w hw
            have hwq0 : w ≠ q₀ := ne_q₀_of_theta_pos (by omega : 0 < (w - q₀).val)
            rw [sbtw_theta hlq0 hwq0 hfq0 (hwl w hw).symm (hwf w hw) hflne]
            rintro (⟨i1, i2⟩ | ⟨i1, i2⟩ | ⟨i1, i2⟩)
            · omega
            · omega
            · omega
          have hDeq : D' = (lPos, fPos) := Prod.ext h2.symm h1.symm
          rw [hDeq]
          intro h
          rcases h with ⟨g1, -, -, -⟩ | ⟨-, -, g3, -⟩
          · exact (ekey A.1 (Or.inl rfl)) g1
          · exact (ekey B.1 (Or.inr (Or.inr (Or.inl rfl)))) g3
        · exact absurd (h1.trans h2.symm) hflne
      have hnotop : A.2 ≠ σ topLabelN ∧ B.2 ≠ σ topLabelN ∧ D'.2 ≠ σ topLabelN := by
        refine ⟨?_, ?_, hD'2top⟩
        · rcases hqcases with ⟨g0, g1⟩ | ⟨g0, g1⟩
          · rw [← g1]
            exact hA2q1
          · rw [← g0]
            exact hA2q0
        · rcases hqcases with ⟨g0, g1⟩ | ⟨g0, g1⟩
          · rw [← g1]
            exact hB2q1
          · rw [← g0]
            exact hB2q0
      have hnal' : ¬ (ChordSep A B D' ∨ ChordSep B A D' ∨ ChordSep D' A B) := by
        rw [not_or, not_or]
        exact ⟨fun h => hnal1 (eA.mpr h), fun h => hnal2 (eB.mpr h), hnsD⟩
      exact aligned_step_del hN hσ ih hA hB hD'mem hAB (fun h => hDB h.symm)
        (fun h => hDA h.symm) kChords_disjoint
        hnotop hnal'

/-- The D/E core of the Claim's inductive step, dispatching on `t` versus `N - 1`.
The case `t > N - 1` is reduced to `t < N - 1` by the beauty-preserving relabelling
`x ↦ N - 1 - x` (which sends `t`-chords to `(2(N-1) - t)`-chords). -/
theorem aligned_step_DE {N : ℕ} [NeZero N] [NeZero (N - 1)] {σ : ZMod N ≃ ZMod N}
    (hN : 4 ≤ N) (hσ : Beautiful σ)
    (ih : ∀ M < N, ∀ [NeZero M], ∀ σ' : ZMod M ≃ ZMod M, Beautiful σ' →
      ∀ k : ℕ, ChordAligned (kChords σ' k))
    {A B C : Chord N} (hA : A ∈ kChords σ (N - 1)) (hB : B ∈ kChords σ (N - 1))
    (hC : C ∈ kChords σ (N - 1)) (hAB : A ≠ B) (hBC : B ≠ C) (hAC : A ≠ C)
    (hC0 : C.1 = σ 0) (hC1 : C.2 = σ topLabelN)
    {q₀ q₁ fPos lPos : ZMod N} (hqq : q₀ ≠ q₁)
    (hq0 : q₀ = σ 0 ∨ q₀ = σ topLabelN) (hq1 : q₁ = σ 0 ∨ q₁ = σ topLabelN)
    (hside : ∀ x : ZMod N, x = A.1 ∨ x = A.2 ∨ x = B.1 ∨ x = B.2 → sbtw q₀ x q₁)
    (hfmem : sbtw q₀ fPos q₁) (hlmem : sbtw q₀ lPos q₁)
    (hfmin : ∀ x : ZMod N, sbtw q₀ x q₁ → (fPos - q₀).val ≤ (x - q₀).val)
    (hlmax : ∀ x : ZMod N, sbtw q₀ x q₁ → (x - q₀).val ≤ (lPos - q₀).val)
    (hfl : (fPos - q₀).val < (lPos - q₀).val)
    (hnal : ¬ (ChordSep A B C ∨ ChordSep B A C ∨ ChordSep C A B)) : False := by
  set t := (σ.symm fPos).val + (σ.symm lPos).val with htdef
  rcases lt_trichotomy t (N - 1) with hlt | heq | hgt
  · exact aligned_step_DE_lt hN hσ ih hA hB hC hAB hBC hAC hC0 hC1 hqq hq0 hq1 hside
      hfmem hlmem hfmin hlmax hfl hlt hnal
  · exact aligned_step_DE_eq hN hσ ih hA hB hC hAB hBC hAC hC0 hC1 hqq hq0 hq1 hside
      hfmem hlmem hfmin hlmax hfl heq hnal
  · -- t > N - 1: transport to the reflected arrangement
    set σ' := negLabelEquiv.trans σ with hσ'def
    have hσ'b : Beautiful σ' := hσ.negLabel
    obtain ⟨xa, ya, hsa, hlea, hAe⟩ := mem_kChords.mp hA
    obtain ⟨xb, yb, hsb, hleb, hBe⟩ := mem_kChords.mp hB
    obtain ⟨xc, yc, hsc, hlec, hCe⟩ := mem_kChords.mp hC
    have nval : ∀ z : ZMod N, (negLabelEquiv.symm z).val = N - 1 - z.val := by
      intro z
      have h2 := negLabel_val (negLabelEquiv.symm z)
      rw [negLabelEquiv.apply_symm_apply] at h2
      have h3 := ZMod.val_lt z
      have h4 := ZMod.val_lt (negLabelEquiv.symm z)
      omega
    have hσ'app : ∀ z : ZMod N, σ' (negLabelEquiv.symm z) = σ z := by
      intro z
      rw [hσ'def]
      show σ (negLabelEquiv (negLabelEquiv.symm z)) = σ z
      rw [negLabelEquiv.apply_symm_apply]
    have mem' : ∀ x y : ZMod N, x.val + y.val = N - 1 → x.val ≤ y.val →
        ((σ y, σ x) : Chord N) ∈ kChords σ' (N - 1) := by
      intro x y hs hle
      rw [mem_kChords]
      refine ⟨negLabelEquiv.symm y, negLabelEquiv.symm x, ?_, ?_, ?_⟩
      · rw [nval, nval]
        omega
      · rw [nval, nval]
        omega
      · rw [hσ'app, hσ'app]
    have hA' : (A.2, A.1) ∈ kChords σ' (N - 1) := by
      rw [hAe]
      exact mem' xa ya hsa hlea
    have hB' : (B.2, B.1) ∈ kChords σ' (N - 1) := by
      rw [hBe]
      exact mem' xb yb hsb hleb
    have hC' : (C.2, C.1) ∈ kChords σ' (N - 1) := by
      rw [hCe]
      exact mem' xc yc hsc hlec
    have e0 : negLabelEquiv (0 : ZMod N) = topLabelN := by
      show (((N - 1 - (0 : ZMod N).val : ℕ)) : ZMod N) = topLabelN
      rw [ZMod.val_zero, Nat.sub_zero]
      rfl
    have etop : negLabelEquiv (topLabelN : ZMod N) = 0 := by
      show (((N - 1 - (topLabelN : ZMod N).val : ℕ)) : ZMod N) = 0
      rw [topLabelN_val, Nat.sub_self, Nat.cast_zero]
    have hC'0 : (C.2, C.1).1 = σ' 0 := by
      show C.2 = σ' 0
      rw [hC1, hσ'def]
      show σ topLabelN = σ (negLabelEquiv 0)
      rw [e0]
    have hC'1 : (C.2, C.1).2 = σ' topLabelN := by
      show C.1 = σ' topLabelN
      rw [hC0, hσ'def]
      show σ 0 = σ (negLabelEquiv topLabelN)
      rw [etop]
    have hq0' : q₀ = σ' 0 ∨ q₀ = σ' topLabelN := by
      rcases hq0 with h | h
      · exact Or.inr (by
          rw [h, hσ'def]
          show σ 0 = σ (negLabelEquiv topLabelN)
          rw [etop])
      · exact Or.inl (by
          rw [h, hσ'def]
          show σ topLabelN = σ (negLabelEquiv 0)
          rw [e0])
    have hq1' : q₁ = σ' 0 ∨ q₁ = σ' topLabelN := by
      rcases hq1 with h | h
      · exact Or.inr (by
          rw [h, hσ'def]
          show σ 0 = σ (negLabelEquiv topLabelN)
          rw [etop])
      · exact Or.inl (by
          rw [h, hσ'def]
          show σ topLabelN = σ (negLabelEquiv 0)
          rw [e0])
    have hside' : ∀ x : ZMod N, x = (A.2, A.1).1 ∨ x = (A.2, A.1).2 ∨
        x = (B.2, B.1).1 ∨ x = (B.2, B.1).2 → sbtw q₀ x q₁ := by
      intro x hx
      apply hside x
      rcases hx with rfl | rfl | rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (Or.inr rfl))
      · exact Or.inr (Or.inr (Or.inl rfl))
    have ht' : (σ'.symm fPos).val + (σ'.symm lPos).val < N - 1 := by
      have hsymm : ∀ z : ZMod N, σ'.symm z = negLabelEquiv.symm (σ.symm z) := by
        intro z
        rw [hσ'def, Equiv.symm_trans]
        rfl
      have hfv := ZMod.val_lt (σ.symm fPos)
      have hlv := ZMod.val_lt (σ.symm lPos)
      rw [hsymm, hsymm, nval, nval]
      omega
    have hnal' : ¬ (ChordSep (A.2, A.1) (B.2, B.1) (C.2, C.1) ∨
        ChordSep (B.2, B.1) (A.2, A.1) (C.2, C.1) ∨
        ChordSep (C.2, C.1) (A.2, A.1) (B.2, B.1)) := by
      obtain ⟨dAB1, dAB2, dAB3, dAB4⟩ := kChords_disjoint A hA B hB hAB
      obtain ⟨dAC1, dAC2, dAC3, dAC4⟩ := kChords_disjoint A hA C hC hAC
      obtain ⟨dBC1, dBC2, dBC3, dBC4⟩ := kChords_disjoint B hB C hC hBC
      rw [not_or, not_or] at hnal
      obtain ⟨g1, g2, g3⟩ := hnal
      rw [not_or, not_or]
      refine ⟨?_, ?_, ?_⟩
      · exact fun h => g1 ((ChordSep.swap_all A B C dAB1 dAB2 dAC1 dAC2 dAB3 dAB4 dAC3 dAC4).mp h)
      · exact fun h => g2 ((ChordSep.swap_all B A C (fun i => dAB1 i.symm) (fun i => dAB3 i.symm)
          dBC1 dBC2 (fun i => dAB2 i.symm) (fun i => dAB4 i.symm) dBC3 dBC4).mp h)
      · exact fun h => g3 ((ChordSep.swap_all C A B (fun i => dAC1 i.symm) (fun i => dAC3 i.symm)
          (fun i => dBC1 i.symm) (fun i => dBC3 i.symm) (fun i => dAC2 i.symm)
          (fun i => dAC4 i.symm) (fun i => dBC2 i.symm) (fun i => dBC4 i.symm)).mp h)
    have hAB' : (A.2, A.1) ≠ (B.2, B.1) := by
      intro h
      obtain ⟨h1, h2⟩ := Prod.ext_iff.mp h
      exact hAB (Prod.ext h2 h1)
    have hBC' : (B.2, B.1) ≠ (C.2, C.1) := by
      intro h
      obtain ⟨h1, h2⟩ := Prod.ext_iff.mp h
      exact hBC (Prod.ext h2 h1)
    have hAC' : (A.2, A.1) ≠ (C.2, C.1) := by
      intro h
      obtain ⟨h1, h2⟩ := Prod.ext_iff.mp h
      exact hAC (Prod.ext h2 h1)
    exact aligned_step_DE_lt hN hσ'b ih hA' hB' hC' hAB' hBC' hAC' hC'0 hC'1 hqq hq0' hq1'
      hside' hfmem hlmem hfmin hlmax hfl ht' hnal'

/-- The Claim's inductive step when one of the three chords is `{0, top}`: the two
remaining chords lie on the same side of `C` (otherwise `C` separates them), and the
D/E core applies on that arc. -/
theorem aligned_step_zerotop {N : ℕ} [NeZero N] [NeZero (N - 1)] {σ : ZMod N ≃ ZMod N}
    (hN : 4 ≤ N) (hσ : Beautiful σ)
    (ih : ∀ M < N, ∀ [NeZero M], ∀ σ' : ZMod M ≃ ZMod M, Beautiful σ' →
      ∀ k : ℕ, ChordAligned (kChords σ' k))
    {A B C : Chord N} (hA : A ∈ kChords σ (N - 1)) (hB : B ∈ kChords σ (N - 1))
    (hC : C ∈ kChords σ (N - 1)) (hAB : A ≠ B) (hBC : B ≠ C) (hAC : A ≠ C)
    (hC0 : C.1 = σ 0) (hC1 : C.2 = σ topLabelN)
    (hnal : ¬ (ChordSep A B C ∨ ChordSep B A C ∨ ChordSep C A B)) : False := by
  rw [not_or, not_or] at hnal
  obtain ⟨hnal1, hnal2, hnal3⟩ := hnal
  obtain ⟨dAC1, dAC2, dAC3, dAC4⟩ := kChords_disjoint A hA C hC hAC
  obtain ⟨dBC1, dBC2, dBC3, dBC4⟩ := kChords_disjoint B hB C hC hBC
  have hnc := Beautiful.kChords_nonCrossing hσ (N - 1)
  have ncA : sbtw C.1 A.1 C.2 ↔ sbtw C.1 A.2 C.2 := hnc C hC A hA (fun h => hAC h.symm)
  have ncB : sbtw C.1 B.1 C.2 ↔ sbtw C.1 B.2 C.2 := hnc C hC B hB (fun h => hBC h.symm)
  have hC12 : C.1 ≠ C.2 := by
    rw [hC0, hC1]
    intro h
    have h1 : (0 : ZMod N) = topLabelN := σ.injective h
    have h2 : (0 : ZMod N).val = (topLabelN : ZMod N).val := by rw [h1]
    rw [ZMod.val_zero, topLabelN_val] at h2
    omega
  have flip : ∀ x : ZMod N, x ≠ C.1 → x ≠ C.2 → ¬ sbtw C.1 x C.2 → sbtw C.2 x C.1 := by
    intro x hx1 hx2 h
    exact (sbtw_not_reverse (fun h' => hx2 h'.symm) hx1 hC12).mpr h
  have core : ∀ q₀ q₁ : ZMod N, q₀ ≠ q₁ →
      (q₀ = σ 0 ∨ q₀ = σ topLabelN) → (q₁ = σ 0 ∨ q₁ = σ topLabelN) →
      (∀ x : ZMod N, x = A.1 ∨ x = A.2 ∨ x = B.1 ∨ x = B.2 → sbtw q₀ x q₁) → False := by
    intro q₀ q₁ hqq hq0 hq1 hside
    set S : Finset (ZMod N) := Finset.univ.filter fun x => sbtw q₀ x q₁ with hSdef
    have hneS : S.Nonempty := ⟨A.1, by
      rw [hSdef, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hside A.1 (Or.inl rfl)⟩⟩
    obtain ⟨fPos, hfmemS, hfmin'⟩ := Finset.exists_min_image S (fun x => (x - q₀).val) hneS
    obtain ⟨lPos, hlmemS, hlmax'⟩ := Finset.exists_max_image S (fun x => (x - q₀).val) hneS
    have hfmem : sbtw q₀ fPos q₁ := (Finset.mem_filter.mp hfmemS).2
    have hlmem : sbtw q₀ lPos q₁ := (Finset.mem_filter.mp hlmemS).2
    have hfmin : ∀ x : ZMod N, sbtw q₀ x q₁ → (fPos - q₀).val ≤ (x - q₀).val := by
      intro x hx
      exact hfmin' x (by rw [hSdef, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hx⟩)
    have hlmax : ∀ x : ZMod N, sbtw q₀ x q₁ → (x - q₀).val ≤ (lPos - q₀).val := by
      intro x hx
      exact hlmax' x (by rw [hSdef, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hx⟩)
    have hfl : (fPos - q₀).val < (lPos - q₀).val := by
      have hle := hfmin lPos hlmem
      rcases eq_or_ne ((fPos - q₀).val) ((lPos - q₀).val) with heq | hne
      · exfalso
        have hall : ∀ x : ZMod N, sbtw q₀ x q₁ → (x - q₀).val = (fPos - q₀).val := by
          intro x hx
          have h1 := hfmin x hx
          have h2 := hlmax x hx
          omega
        have hA1s := hside A.1 (Or.inl rfl)
        have hA2s := hside A.2 (Or.inr (Or.inl rfl))
        have hB1s := hside B.1 (Or.inr (Or.inr (Or.inl rfl)))
        have hB2s := hside B.2 (Or.inr (Or.inr (Or.inr rfl)))
        have e1 : A.1 = B.1 := theta_inj ((hall A.1 hA1s).trans (hall B.1 hB1s).symm)
        obtain ⟨dAB1, -, -, -⟩ := kChords_disjoint A hA B hB hAB
        exact dAB1 e1
      · exact lt_of_le_of_ne hle hne
    exact aligned_step_DE hN hσ ih hA hB hC hAB hBC hAC hC0 hC1 hqq hq0 hq1 hside
      hfmem hlmem hfmin hlmax hfl (by
        rw [not_or, not_or]
        exact ⟨hnal1, hnal2, hnal3⟩)
  by_cases hAL : sbtw C.1 A.1 C.2
  · by_cases hBL : sbtw C.1 B.1 C.2
    · -- A, B on the C.1 → C.2 arc
      exact core C.1 C.2 hC12 (Or.inl hC0) (Or.inr hC1) (by
        intro x hx
        rcases hx with rfl | rfl | rfl | rfl
        · exact hAL
        · exact ncA.mp hAL
        · exact hBL
        · exact ncB.mp hBL)
    · -- A left, B right: C separates them
      exact hnal3 (Or.inl ⟨hAL, ncA.mp hAL, hBL, fun h => hBL (ncB.mpr h)⟩)
  · by_cases hBL : sbtw C.1 B.1 C.2
    · -- A right, B left: C separates them
      exact hnal3 (Or.inr ⟨hAL, fun h => hAL (ncA.mpr h), hBL, ncB.mp hBL⟩)
    · -- A, B on the C.2 → C.1 arc
      exact core C.2 C.1 (fun h => hC12 h.symm) (Or.inr hC1) (Or.inl hC0) (by
        intro x hx
        rcases hx with rfl | rfl | rfl | rfl
        · exact flip A.1 dAC1 dAC2 hAL
        · exact flip A.2 dAC3 dAC4 (fun h => hAL (ncA.mpr h))
        · exact flip B.1 dBC1 dBC2 hBL
        · exact flip B.2 dBC3 dBC4 (fun h => hBL (ncB.mpr h)))

/-- The main structural claim: in a beautiful arrangement, the chords of any given
sum are aligned. -/
theorem aligned_kChords : ∀ N : ℕ, ∀ [NeZero N], ∀ σ : ZMod N ≃ ZMod N,
    Beautiful σ → ∀ k : ℕ, ChordAligned (kChords σ k) := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro hN σ hσ k
    by_cases hm : N ≤ 3
    · exact ChordAligned.of_card_le_two (kChords_card_le_two hm σ k)
    · haveI : NeZero (N - 1) := ⟨by omega⟩
      intro A hA B hB C hC hAB hBC hAC
      by_contra hnal
      by_cases htop : A.2 = σ topLabelN ∨ B.2 = σ topLabelN ∨ C.2 = σ topLabelN
      · by_cases hzero : A.1 = σ 0 ∨ B.1 = σ 0 ∨ C.1 = σ 0
        · -- both extremal labels appear: then k = N - 1 and one chord is {0, top}
          have key_top : ∀ X : Chord N, X ∈ kChords σ k → X.2 = σ topLabelN → N - 1 ≤ k := by
            intro X hX hX2
            obtain ⟨x, y, hs, hle, hXX⟩ := mem_kChords.mp hX
            have hy : y = topLabelN := by
              apply σ.injective
              have h1 : X.2 = σ y := by rw [hXX]
              rw [h1] at hX2
              exact hX2
            have hyv : y.val = N - 1 := by rw [hy, topLabelN_val]
            omega
          have key_zero : ∀ X : Chord N, X ∈ kChords σ k → X.1 = σ 0 → k ≤ N - 1 := by
            intro X hX hX1
            obtain ⟨x, y, hs, hle, hXX⟩ := mem_kChords.mp hX
            have hx : x = 0 := by
              apply σ.injective
              have h1 : X.1 = σ x := by rw [hXX]
              rw [h1] at hX1
              exact hX1
            have hxv : x.val = 0 := by rw [hx, ZMod.val_zero]
            have := ZMod.val_lt y
            omega
          have hk : k = N - 1 := by
            rcases htop with ht | ht | ht <;> rcases hzero with hz | hz | hz
            · exact le_antisymm (key_zero A hA hz) (key_top A hA ht)
            · exact le_antisymm (key_zero B hB hz) (key_top A hA ht)
            · exact le_antisymm (key_zero C hC hz) (key_top A hA ht)
            · exact le_antisymm (key_zero A hA hz) (key_top B hB ht)
            · exact le_antisymm (key_zero B hB hz) (key_top B hB ht)
            · exact le_antisymm (key_zero C hC hz) (key_top B hB ht)
            · exact le_antisymm (key_zero A hA hz) (key_top C hC ht)
            · exact le_antisymm (key_zero B hB hz) (key_top C hC ht)
            · exact le_antisymm (key_zero C hC hz) (key_top C hC ht)
          subst hk
          have special : ∀ X : Chord N, X ∈ kChords σ (N - 1) → X.2 = σ topLabelN →
              X.1 = σ 0 := by
            intro X hX hX2
            obtain ⟨x, y, hs, hle, hXX⟩ := mem_kChords.mp hX
            have hy : y = topLabelN := by
              apply σ.injective
              have h1 : X.2 = σ y := by rw [hXX]
              rw [h1] at hX2
              exact hX2
            have hyv : y.val = N - 1 := by rw [hy, topLabelN_val]
            have hxv : x.val = 0 := by omega
            have hx : x = 0 := by
              rw [← ZMod.natCast_zmod_val x, hxv, Nat.cast_zero]
            rw [hXX, hx]
          rcases htop with ht | ht | ht
          · -- A is the {0, top} chord
            rw [not_or, not_or] at hnal
            obtain ⟨g1, g2, g3⟩ := hnal
            exact aligned_step_zerotop (by omega) hσ ih hB hC hA hBC (fun h => hAC h.symm)
              (fun h => hAB h.symm) (special A hA ht) ht (by
              rw [not_or, not_or]
              exact ⟨fun h => g2 ((ChordSep.flip B C A).mp h),
                fun h => g3 ((ChordSep.flip C B A).mp h), fun h => g1 h⟩)
          · -- B is the {0, top} chord
            rw [not_or, not_or] at hnal
            obtain ⟨g1, g2, g3⟩ := hnal
            exact aligned_step_zerotop (by omega) hσ ih hA hC hB hAC (fun h => hBC h.symm)
              hAB (special B hB ht) ht (by
              rw [not_or, not_or]
              exact ⟨fun h => g1 ((ChordSep.flip A C B).mp h), fun h => g3 h,
                fun h => g2 h⟩)
          · -- C is the {0, top} chord
            exact aligned_step_zerotop (by omega) hσ ih hA hB hC hAB hBC hAC
              (special C hC ht) ht hnal
        · exact aligned_step_delzero (by omega) hσ ih hA hB hC hAB hBC hAC kChords_disjoint
            ⟨fun h => hzero (Or.inl h), fun h => hzero (Or.inr (Or.inl h)),
              fun h => hzero (Or.inr (Or.inr h))⟩ hnal
      · exact aligned_step_del (by omega) hσ ih hA hB hC hAB hBC hAC kChords_disjoint
          ⟨fun h => htop (Or.inl h), fun h => htop (Or.inr (Or.inl h)),
            fun h => htop (Or.inr (Or.inr h))⟩ hnal

/-! ## The parallel extension condition -/

/-- Beauty is equivalent to pairwise non-crossing of every chord family. -/
theorem beautiful_of_nonCrossing {N : ℕ} [NeZero N] {σ : ZMod N ≃ ZMod N}
    (h : ∀ k : ℕ, ChordNonCrossing (kChords σ k)) : Beautiful σ := by
  intro a b c d hab hbc hcd hsum hc
  have hmem1 : (σ a, σ d) ∈ kChords σ (a.val + d.val) := by
    rw [mem_kChords]
    exact ⟨a, d, rfl, by omega, rfl⟩
  have hmem2 : (σ b, σ c) ∈ kChords σ (a.val + d.val) := by
    rw [mem_kChords]
    exact ⟨b, c, by omega, by omega, rfl⟩
  have hne : (σ a, σ d) ≠ (σ b, σ c) := by
    intro he
    obtain ⟨h1, -⟩ := Prod.ext_iff.mp he
    have h2 : a = b := σ.injective h1
    rw [h2] at hab
    exact lt_irrefl _ hab
  have hnc := h (a.val + d.val) (σ a, σ d) hmem1 (σ b, σ c) hmem2 hne
  unfold Crossing at hc
  exact hc (propext hnc)

/-! ## Constant-sum chord families are aligned -/

/-- Subtraction by a fixed amount preserves strict betweenness (general-modulus
version of `sbtw_sub`). -/
theorem sbtw_sub' {N : ℕ} [NeZero N] {a b c : ZMod N} (t : ZMod N) (hab : a ≠ b) :
    sbtw (a - t) (b - t) (c - t) ↔ sbtw a b c := by
  have h := sbtw_add (-t) hab (a := a) (b := b) (c := c)
  simpa [sub_eq_add_neg] using h

/-- `ChordSep` is invariant under simultaneous translation of all endpoints
(general-modulus version of `ChordSep_sub`). -/
theorem ChordSep_sub' {N : ℕ} [NeZero N] {A₁ A₂ B₁ B₂ C₁ C₂ : ZMod N} (t : ZMod N)
    (hAB1 : A₁ ≠ B₁) (hAB2 : A₁ ≠ B₂) (hAC1 : A₁ ≠ C₁) (hAC2 : A₁ ≠ C₂) :
    ChordSep (A₁ - t, A₂ - t) (B₁ - t, B₂ - t) (C₁ - t, C₂ - t) ↔
    ChordSep (A₁, A₂) (B₁, B₂) (C₁, C₂) := by
  unfold ChordSep
  rw [sbtw_sub' t hAB1, sbtw_sub' t hAB2, sbtw_sub' t hAC1, sbtw_sub' t hAC2]

/-- Two disjoint chords of endpoint-sum `0`, non-crossing with each other, versus
the degenerate chord `(0, 0)`: one of them separates `(0, 0)` from the other.
This is the degenerate-`A` case of `chordSep_of_const_sum_zero`. -/
theorem chordSep_of_sum_zero {N : ℕ} [NeZero N] {b₁ b₂ c₁ c₂ : ZMod N}
    (hsumB : b₁ + b₂ = 0) (hsumC : c₁ + c₂ = 0)
    (hb10 : b₁ ≠ 0) (hb20 : b₂ ≠ 0) (hc10 : c₁ ≠ 0) (hc20 : c₂ ≠ 0)
    (hbc11 : b₁ ≠ c₁) (hbc12 : b₁ ≠ c₂) (hbc21 : b₂ ≠ c₁) (hbc22 : b₂ ≠ c₂)
    (hncBC : sbtw b₁ c₁ b₂ ↔ sbtw b₁ c₂ b₂) (hncCB : sbtw c₁ b₁ c₂ ↔ sbtw c₁ b₂ c₂) :
    ChordSep (b₁, b₂) (0, 0) (c₁, c₂) ∨ ChordSep (c₁, c₂) (0, 0) (b₁, b₂) := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hb1l := ZMod.val_lt b₁
  have hb2l := ZMod.val_lt b₂
  have hc1l := ZMod.val_lt c₁
  have hc2l := ZMod.val_lt c₂
  have vz : ∀ x : ZMod N, x.val = 0 → x = 0 := by
    intro x h
    rw [← ZMod.natCast_zmod_val x, h, Nat.cast_zero]
  have d : ∀ x y : ZMod N, x ≠ y → x.val ≠ y.val :=
    fun x y h he => h (ZMod.val_injective _ he)
  have vb10 : b₁.val ≠ 0 := fun h => hb10 (vz b₁ h)
  have vb20 : b₂.val ≠ 0 := fun h => hb20 (vz b₂ h)
  have vc10 : c₁.val ≠ 0 := fun h => hc10 (vz c₁ h)
  have vc20 : c₂.val ≠ 0 := fun h => hc20 (vz c₂ h)
  have vbc11 := d b₁ c₁ hbc11
  have vbc12 := d b₁ c₂ hbc12
  have vbc21 := d b₂ c₁ hbc21
  have vbc22 := d b₂ c₂ hbc22
  have hsumB' : b₁.val + b₂.val = N := by
    have h : ((b₁.val + b₂.val : ℕ) : ZMod N) = 0 := by
      rw [Nat.cast_add, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
      exact hsumB
    have h2 := congrArg ZMod.val h
    rw [ZMod.val_natCast, ZMod.val_zero] at h2
    by_cases hlt : b₁.val + b₂.val < N
    · rw [Nat.mod_eq_of_lt hlt] at h2
      omega
    · have hsub : (b₁.val + b₂.val) % N = b₁.val + b₂.val - N := by
        rw [Nat.mod_eq_sub_mod (Nat.le_of_not_lt hlt), Nat.mod_eq_of_lt (by omega)]
      rw [hsub] at h2
      omega
  have hsumC' : c₁.val + c₂.val = N := by
    have h : ((c₁.val + c₂.val : ℕ) : ZMod N) = 0 := by
      rw [Nat.cast_add, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
      exact hsumC
    have h2 := congrArg ZMod.val h
    rw [ZMod.val_natCast, ZMod.val_zero] at h2
    by_cases hlt : c₁.val + c₂.val < N
    · rw [Nat.mod_eq_of_lt hlt] at h2
      omega
    · have hsub : (c₁.val + c₂.val) % N = c₁.val + c₂.val - N := by
        rw [Nat.mod_eq_sub_mod (Nat.le_of_not_lt hlt), Nat.mod_eq_of_lt (by omega)]
      rw [hsub] at h2
      omega
  -- the point `0` lies on exactly one of the two `sbtw`-arcs
  have key : ¬ (sbtw b₁ 0 b₂ ↔ sbtw b₁ c₁ b₂) ∨
      ¬ (sbtw c₁ 0 c₂ ↔ sbtw c₁ b₁ c₂) := by
    by_cases hb : b₁.val ≤ b₂.val <;> by_cases hc : c₁.val ≤ c₂.val
    · simp only [sbtw_of_val_le hb, sbtw_of_val_le hc, ZMod.val_zero]
      omega
    · simp only [sbtw_of_val_le hb,
        sbtw_of_val_gt (by omega : c₂.val < c₁.val), ZMod.val_zero]
      omega
    · simp only [sbtw_of_val_gt (by omega : b₂.val < b₁.val),
        sbtw_of_val_le hc, ZMod.val_zero]
      omega
    · simp only [sbtw_of_val_gt (by omega : b₂.val < b₁.val),
        sbtw_of_val_gt (by omega : c₂.val < c₁.val), ZMod.val_zero]
      omega
  rcases key with hkk | hkk
  · refine Or.inl ?_
    by_cases hp : sbtw b₁ 0 b₂ <;> by_cases hq : sbtw b₁ c₁ b₂
    · exact absurd ⟨fun _ => hq, fun _ => hp⟩ hkk
    · exact Or.inl ⟨hp, hp, hq, fun hq2 => hq (hncBC.mpr hq2)⟩
    · exact Or.inr ⟨hp, hp, hq, hncBC.mp hq⟩
    · exact absurd ⟨fun h => absurd h hp, fun h => absurd h hq⟩ hkk
  · refine Or.inr ?_
    by_cases hp : sbtw c₁ 0 c₂ <;> by_cases hq : sbtw c₁ b₁ c₂
    · exact absurd ⟨fun _ => hq, fun _ => hp⟩ hkk
    · exact Or.inl ⟨hp, hp, hq, fun hq2 => hq (hncCB.mpr hq2)⟩
    · exact Or.inr ⟨hp, hp, hq, hncCB.mp hq⟩
    · exact absurd ⟨fun h => absurd h hp, fun h => absurd h hq⟩ hkk

/-- Two chords on the same arc of `(0, a)`, with equal endpoint-value sums and all
endpoints distinct, are nested: the outer one separates `(0, a)` from the inner
one.  The conclusion is `ChordSep (x₁, x₂) (0, a) (y₁, y₂) ∨
ChordSep (y₁, y₂) (0, a) (x₁, x₂)`, written out for a smoother proof. -/
theorem chordSep_zero_nested {N : ℕ} [NeZero N] {a : ZMod N} (x₁ x₂ y₁ y₂ : ZMod N)
    (s : ℕ) (hsumx : x₁.val + x₂.val = s) (hsumy : y₁.val + y₂.val = s)
    (houtx : (x₁.val < a.val ∧ x₂.val < a.val) ∨ (a.val < x₁.val ∧ a.val < x₂.val))
    (houty : (y₁.val < a.val ∧ y₂.val < a.val) ∨ (a.val < y₁.val ∧ a.val < y₂.val))
    (hx10 : x₁.val ≠ 0) (hx20 : x₂.val ≠ 0) (hy10 : y₁.val ≠ 0) (hy20 : y₂.val ≠ 0)
    (hne11 : x₁.val ≠ y₁.val) (hne12 : x₁.val ≠ y₂.val)
    (hne21 : x₂.val ≠ y₁.val) (hne22 : x₂.val ≠ y₂.val) :
    ((sbtw x₁ 0 x₂ ∧ sbtw x₁ a x₂ ∧ ¬ sbtw x₁ y₁ x₂ ∧ ¬ sbtw x₁ y₂ x₂) ∨
      (¬ sbtw x₁ 0 x₂ ∧ ¬ sbtw x₁ a x₂ ∧ sbtw x₁ y₁ x₂ ∧ sbtw x₁ y₂ x₂)) ∨
    ((sbtw y₁ 0 y₂ ∧ sbtw y₁ a y₂ ∧ ¬ sbtw y₁ x₁ y₂ ∧ ¬ sbtw y₁ x₂ y₂) ∨
      (¬ sbtw y₁ 0 y₂ ∧ ¬ sbtw y₁ a y₂ ∧ sbtw y₁ x₁ y₂ ∧ sbtw y₁ x₂ y₂)) := by
  have hal := ZMod.val_lt a
  have hx1l := ZMod.val_lt x₁
  have hx2l := ZMod.val_lt x₂
  have hy1l := ZMod.val_lt y₁
  have hy2l := ZMod.val_lt y₂
  by_cases hx : x₁.val ≤ x₂.val <;> by_cases hy : y₁.val ≤ y₂.val
  · by_cases hm : x₁.val < y₁.val
    · refine Or.inl (Or.inr ⟨?_, ?_, ?_, ?_⟩) <;>
        simp only [sbtw_of_val_le hx, ZMod.val_zero] <;> omega
    · refine Or.inr (Or.inr ⟨?_, ?_, ?_, ?_⟩) <;>
        simp only [sbtw_of_val_le hy, ZMod.val_zero] <;> omega
  · by_cases hm : x₁.val < y₂.val
    · refine Or.inl (Or.inr ⟨?_, ?_, ?_, ?_⟩) <;>
        simp only [sbtw_of_val_le hx, ZMod.val_zero] <;> omega
    · refine Or.inr (Or.inl ⟨?_, ?_, ?_, ?_⟩) <;>
        simp only [sbtw_of_val_gt (by omega : y₂.val < y₁.val), ZMod.val_zero] <;> omega
  · by_cases hm : x₂.val < y₁.val
    · refine Or.inl (Or.inl ⟨?_, ?_, ?_, ?_⟩) <;>
        simp only [sbtw_of_val_gt (by omega : x₂.val < x₁.val), ZMod.val_zero] <;> omega
    · refine Or.inr (Or.inr ⟨?_, ?_, ?_, ?_⟩) <;>
        simp only [sbtw_of_val_le hy, ZMod.val_zero] <;> omega
  · by_cases hm : x₂.val < y₂.val
    · refine Or.inl (Or.inl ⟨?_, ?_, ?_, ?_⟩) <;>
        simp only [sbtw_of_val_gt (by omega : x₂.val < x₁.val), ZMod.val_zero] <;> omega
    · refine Or.inr (Or.inl ⟨?_, ?_, ?_, ?_⟩) <;>
        simp only [sbtw_of_val_gt (by omega : y₂.val < y₁.val), ZMod.val_zero] <;> omega

/-- Normalized triple lemma: for the chord `A = (0, a)` and two further chords
`(b₁, b₂)`, `(c₁, c₂)` with the same endpoint-sum `a`, all pairwise disjoint, with
`(b₁, b₂)` and `(c₁, c₂)` each non-crossing with `A` and with each other, one of
the three chords separates the other two.  The proof is a value case analysis: if
the two chords lie on different open arcs of `A` then `A` separates them; if they
lie on the same arc, their endpoint values are nested (equal sums force
`min + max` to agree), and the outer chord separates `A` from the inner one. -/
theorem chordSep_of_const_sum_zero {N : ℕ} [NeZero N] {a b₁ b₂ c₁ c₂ : ZMod N}
    (hsumB : b₁ + b₂ = a) (hsumC : c₁ + c₂ = a)
    (hb10 : b₁ ≠ 0) (hb20 : b₂ ≠ 0) (hb1a : b₁ ≠ a) (hb2a : b₂ ≠ a)
    (hc10 : c₁ ≠ 0) (hc20 : c₂ ≠ 0) (hc1a : c₁ ≠ a) (hc2a : c₂ ≠ a)
    (hbc11 : b₁ ≠ c₁) (hbc12 : b₁ ≠ c₂) (hbc21 : b₂ ≠ c₁) (hbc22 : b₂ ≠ c₂)
    (hncB : sbtw 0 b₁ a ↔ sbtw 0 b₂ a) (hncC : sbtw 0 c₁ a ↔ sbtw 0 c₂ a)
    (hncBC : sbtw b₁ c₁ b₂ ↔ sbtw b₁ c₂ b₂) (hncCB : sbtw c₁ b₁ c₂ ↔ sbtw c₁ b₂ c₂) :
    ChordSep (0, a) (b₁, b₂) (c₁, c₂) ∨ ChordSep (b₁, b₂) (0, a) (c₁, c₂) ∨
      ChordSep (c₁, c₂) (0, a) (b₁, b₂) := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hal := ZMod.val_lt a
  have hb1l := ZMod.val_lt b₁
  have hb2l := ZMod.val_lt b₂
  have hc1l := ZMod.val_lt c₁
  have hc2l := ZMod.val_lt c₂
  -- endpoint sums as natural-number relations
  have hsumBv : (b₁.val + b₂.val) % N = a.val := by
    have h : ((b₁.val + b₂.val : ℕ) : ZMod N) = a := by
      rw [Nat.cast_add, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
      exact hsumB
    have h2 := congrArg ZMod.val h
    rwa [ZMod.val_natCast] at h2
  have hsumCv : (c₁.val + c₂.val) % N = a.val := by
    have h : ((c₁.val + c₂.val : ℕ) : ZMod N) = a := by
      rw [Nat.cast_add, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
      exact hsumC
    have h2 := congrArg ZMod.val h
    rwa [ZMod.val_natCast] at h2
  have hsumB' : b₁.val + b₂.val = a.val ∨ b₁.val + b₂.val = a.val + N := by
    by_cases hlt : b₁.val + b₂.val < N
    · left
      rw [Nat.mod_eq_of_lt hlt] at hsumBv
      exact hsumBv
    · right
      have hsub : (b₁.val + b₂.val) % N = b₁.val + b₂.val - N := by
        rw [Nat.mod_eq_sub_mod (Nat.le_of_not_lt hlt), Nat.mod_eq_of_lt (by omega)]
      rw [hsub] at hsumBv
      omega
  have hsumC' : c₁.val + c₂.val = a.val ∨ c₁.val + c₂.val = a.val + N := by
    by_cases hlt : c₁.val + c₂.val < N
    · left
      rw [Nat.mod_eq_of_lt hlt] at hsumCv
      exact hsumCv
    · right
      have hsub : (c₁.val + c₂.val) % N = c₁.val + c₂.val - N := by
        rw [Nat.mod_eq_sub_mod (Nat.le_of_not_lt hlt), Nat.mod_eq_of_lt (by omega)]
      rw [hsub] at hsumCv
      omega
  clear hsumBv hsumCv
  -- disjointness as value inequalities
  have vz : ∀ x : ZMod N, x.val = 0 → x = 0 := by
    intro x h
    rw [← ZMod.natCast_zmod_val x, h, Nat.cast_zero]
  have d : ∀ x y : ZMod N, x ≠ y → x.val ≠ y.val :=
    fun x y h he => h (ZMod.val_injective _ he)
  have vb10 : b₁.val ≠ 0 := fun h => hb10 (vz b₁ h)
  have vb20 : b₂.val ≠ 0 := fun h => hb20 (vz b₂ h)
  have vc10 : c₁.val ≠ 0 := fun h => hc10 (vz c₁ h)
  have vc20 : c₂.val ≠ 0 := fun h => hc20 (vz c₂ h)
  have vb1a := d b₁ a hb1a
  have vb2a := d b₂ a hb2a
  have vc1a := d c₁ a hc1a
  have vc2a := d c₂ a hc2a
  have vbc11 := d b₁ c₁ hbc11
  have vbc12 := d b₁ c₂ hbc12
  have vbc21 := d b₂ c₁ hbc21
  have vbc22 := d b₂ c₂ hbc22
  -- `sbtw` from `0` as a value comparison
  have key0 : ∀ x : ZMod N, x ≠ 0 → (sbtw 0 x a ↔ x.val < a.val) := by
    intro x hx
    rw [sbtw_val (show (0 : ZMod N) ≠ x from fun h => hx h.symm), sub_zero, sub_zero]
  have arcB : b₁.val < a.val ↔ b₂.val < a.val :=
    (key0 b₁ hb10).symm.trans (hncB.trans (key0 b₂ hb20))
  have arcC : c₁.val < a.val ↔ c₂.val < a.val :=
    (key0 c₁ hc10).symm.trans (hncC.trans (key0 c₂ hc20))
  by_cases ha0 : a.val = 0
  · -- `A = (0, 0)` degenerate: `B` or `C` separates
    have ha : a = 0 := vz a ha0
    subst ha
    exact Or.inr (chordSep_of_sum_zero hsumB hsumC hb10 hb20 hc10 hc20
      hbc11 hbc12 hbc21 hbc22 hncBC hncCB)
  · -- `A` non-degenerate: arcs of `B` and `C` relative to `(0, a)`
    clear hncBC hncCB
    by_cases hB : b₁.val < a.val
    · have hB2 : b₂.val < a.val := arcB.mp hB
      by_cases hC : c₁.val < a.val
      · -- `B` and `C` on the same inner arc: nested
        have hC2 : c₂.val < a.val := arcC.mp hC
        right
        exact chordSep_zero_nested (a := a) b₁ b₂ c₁ c₂ a.val (by omega) (by omega)
          (Or.inl ⟨hB, hB2⟩) (Or.inl ⟨hC, hC2⟩)
          vb10 vb20 vc10 vc20 vbc11 vbc12 vbc21 vbc22
      · -- `B` inside, `C` outside: `A` separates
        have hC2 : ¬ c₂.val < a.val := fun h => hC (arcC.mpr h)
        left
        exact Or.inl ⟨(key0 b₁ hb10).mpr hB, (key0 b₂ hb20).mpr hB2,
          fun h => hC ((key0 c₁ hc10).mp h), fun h => hC2 ((key0 c₂ hc20).mp h)⟩
    · have hB2 : ¬ b₂.val < a.val := fun h => hB (arcB.mpr h)
      by_cases hC : c₁.val < a.val
      · -- `B` outside, `C` inside: `A` separates
        have hC2 : c₂.val < a.val := arcC.mp hC
        left
        exact Or.inr ⟨fun h => hB ((key0 b₁ hb10).mp h),
          fun h => hB2 ((key0 b₂ hb20).mp h),
          (key0 c₁ hc10).mpr hC, (key0 c₂ hc20).mpr hC2⟩
      · -- `B` and `C` on the same outer arc: nested
        have hC2 : ¬ c₂.val < a.val := fun h => hC (arcC.mpr h)
        right
        exact chordSep_zero_nested (a := a) b₁ b₂ c₁ c₂ (a.val + N) (by omega) (by omega)
          (Or.inr ⟨by omega, by omega⟩) (Or.inr ⟨by omega, by omega⟩)
          vb10 vb20 vc10 vc20 vbc11 vbc12 vbc21 vbc22

/-- Three pairwise disjoint, pairwise non-crossing chords with a common
endpoint-sum: one of the three separates the other two.  Proved by translating
the first chord to `(0, a)` and applying `chordSep_of_const_sum_zero`. -/
theorem chordSep_of_const_sum {N : ℕ} [NeZero N] {A B C : Chord N} {c₀ : ZMod N}
    (hsumA : A.1 + A.2 = c₀) (hsumB : B.1 + B.2 = c₀) (hsumC : C.1 + C.2 = c₀)
    (hdjAB : A.1 ≠ B.1 ∧ A.1 ≠ B.2 ∧ A.2 ≠ B.1 ∧ A.2 ≠ B.2)
    (hdjAC : A.1 ≠ C.1 ∧ A.1 ≠ C.2 ∧ A.2 ≠ C.1 ∧ A.2 ≠ C.2)
    (hdjBC : B.1 ≠ C.1 ∧ B.1 ≠ C.2 ∧ B.2 ≠ C.1 ∧ B.2 ≠ C.2)
    (hncAB : sbtw A.1 B.1 A.2 ↔ sbtw A.1 B.2 A.2)
    (hncAC : sbtw A.1 C.1 A.2 ↔ sbtw A.1 C.2 A.2)
    (hncBC : sbtw B.1 C.1 B.2 ↔ sbtw B.1 C.2 B.2)
    (hncCB : sbtw C.1 B.1 C.2 ↔ sbtw C.1 B.2 C.2) :
    ChordSep A B C ∨ ChordSep B A C ∨ ChordSep C A B := by
  obtain ⟨hdjAB1, hdjAB2, hdjAB3, hdjAB4⟩ := hdjAB
  obtain ⟨hdjAC1, hdjAC2, hdjAC3, hdjAC4⟩ := hdjAC
  obtain ⟨hdjBC1, hdjBC2, hdjBC3, hdjBC4⟩ := hdjBC
  have e0 : A.1 - A.1 = (0 : ZMod N) := sub_self A.1
  have sbinj : ∀ x y : ZMod N, x ≠ y → x - A.1 ≠ y - A.1 := by
    intro x y h he
    apply h
    have h2 := congrArg (· + A.1) he
    simpa only [sub_add_cancel] using h2
  have hsumB' : B.1 - A.1 + (B.2 - A.1) = A.2 - A.1 := by
    linear_combination hsumB - hsumA
  have hsumC' : C.1 - A.1 + (C.2 - A.1) = A.2 - A.1 := by
    linear_combination hsumC - hsumA
  have hncB' : sbtw 0 (B.1 - A.1) (A.2 - A.1) ↔ sbtw 0 (B.2 - A.1) (A.2 - A.1) := by
    rw [← e0, sbtw_sub' A.1 hdjAB1, sbtw_sub' A.1 hdjAB2]
    exact hncAB
  have hncC' : sbtw 0 (C.1 - A.1) (A.2 - A.1) ↔ sbtw 0 (C.2 - A.1) (A.2 - A.1) := by
    rw [← e0, sbtw_sub' A.1 hdjAC1, sbtw_sub' A.1 hdjAC2]
    exact hncAC
  have hncBC' : sbtw (B.1 - A.1) (C.1 - A.1) (B.2 - A.1) ↔
      sbtw (B.1 - A.1) (C.2 - A.1) (B.2 - A.1) := by
    rw [sbtw_sub' A.1 hdjBC1, sbtw_sub' A.1 hdjBC2]
    exact hncBC
  have hncCB' : sbtw (C.1 - A.1) (B.1 - A.1) (C.2 - A.1) ↔
      sbtw (C.1 - A.1) (B.2 - A.1) (C.2 - A.1) := by
    rw [sbtw_sub' A.1 hdjBC1.symm, sbtw_sub' A.1 hdjBC3.symm]
    exact hncCB
  have aux := chordSep_of_const_sum_zero hsumB' hsumC'
    (sub_ne_zero.mpr hdjAB1.symm) (sub_ne_zero.mpr hdjAB2.symm)
    (sbinj B.1 A.2 hdjAB3.symm) (sbinj B.2 A.2 hdjAB4.symm)
    (sub_ne_zero.mpr hdjAC1.symm) (sub_ne_zero.mpr hdjAC2.symm)
    (sbinj C.1 A.2 hdjAC3.symm) (sbinj C.2 A.2 hdjAC4.symm)
    (sbinj B.1 C.1 hdjBC1) (sbinj B.1 C.2 hdjBC2)
    (sbinj B.2 C.1 hdjBC3) (sbinj B.2 C.2 hdjBC4)
    hncB' hncC' hncBC' hncCB'
  rcases aux with h | h | h
  · left
    rw [← e0] at h
    have h2 := (ChordSep_sub' A.1 hdjAB1 hdjAB2 hdjAC1 hdjAC2).mp h
    simpa only [Prod.mk.eta] using h2
  · right; left
    rw [← e0] at h
    have h2 := (ChordSep_sub' A.1 hdjAB1.symm hdjAB3.symm hdjBC1 hdjBC2).mp h
    simpa only [Prod.mk.eta] using h2
  · right; right
    rw [← e0] at h
    have h2 := (ChordSep_sub' A.1 hdjAC1.symm hdjAC3.symm hdjBC1.symm hdjBC3.symm).mp h
    simpa only [Prod.mk.eta] using h2

/-- A pairwise non-crossing, pairwise vertex-disjoint family of chords with a
constant endpoint-sum is aligned: for any three distinct chords of the family,
one separates the other two. -/
theorem ChordAligned_of_const_sum {N : ℕ} [NeZero N] {F : Finset (Chord N)} {c₀ : ZMod N}
    (hnc : ChordNonCrossing F) (hdj : ChordDisjoint F)
    (hsum : ∀ A ∈ F, A.1 + A.2 = c₀) : ChordAligned F := by
  intro A hA B hB C hC hAB hBC hAC
  exact chordSep_of_const_sum (hsum A hA) (hsum B hB) (hsum C hC)
    (hdj A hA B hB hAB) (hdj A hA C hC hAC) (hdj B hB C hC hBC)
    (hnc A hA B hB hAB) (hnc A hA C hC hAC) (hnc B hB C hC hBC) (hnc C hC B hB hBC.symm)

/-- Strict betweenness forces the three points to be distinct. -/
theorem sbtw_ne' {N : ℕ} [NeZero N] {a b c : ZMod N} (h : sbtw a b c) :
    a ≠ b ∧ b ≠ c ∧ a ≠ c := by
  rw [sbtw_zmod_def] at h
  refine ⟨?_, ?_, ?_⟩ <;> intro he <;> subst he <;>
    rcases h with ⟨g1, g2⟩ | ⟨g1, g2⟩ | ⟨g1, g2⟩ <;> omega

/-- Two points on the same open arc from `p` to `q` see `p` and `q` on the same
side. -/
theorem sbtw_same_arc {N : ℕ} [NeZero N] {p q r s : ZMod N}
    (hr : sbtw p r q) (hs : sbtw p s q) : sbtw r p s ↔ sbtw r q s := by
  have hpr := (sbtw_ne' hr).1
  have hps := (sbtw_ne' hs).1
  have hrq := (sbtw_ne' hr).2.1
  rw [sbtw_val hpr.symm, sbtw_val hrq]
  rw [sbtw_val hpr] at hr
  rw [sbtw_val hps] at hs
  have h1rp : 1 ≤ (r - p).val := by
    by_contra h0
    have hz : (r - p).val = 0 := by omega
    have hne : r - p ≠ 0 := sub_ne_zero.mpr hpr.symm
    apply hne
    have e := ZMod.natCast_zmod_val (r - p)
    rw [hz, Nat.cast_zero] at e
    exact e.symm
  have h1sp : 1 ≤ (s - p).val := by
    by_contra h0
    have hz : (s - p).val = 0 := by omega
    have hne : s - p ≠ 0 := sub_ne_zero.mpr hps.symm
    apply hne
    have e := ZMod.natCast_zmod_val (s - p)
    rw [hz, Nat.cast_zero] at e
    exact e.symm
  have hqr : (q - r).val = (q - p).val - (r - p).val := by
    have e : (q - r : ZMod N) = (q - p) - (r - p) := by ring
    rw [e, val_sub']
    have h1 : (q - p).val + N - (r - p).val = ((q - p).val - (r - p).val) + N := by
      omega
    rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by have := ZMod.val_lt (q - p); omega)]
  have hpr' : (p - r).val = N - (r - p).val := by
    have e : (p - r : ZMod N) = -(r - p) := by ring
    rw [e, val_neg'' (sub_ne_zero.mpr hpr.symm)]
  have hsr : (s - r).val = ((s - p).val + N - (r - p).val) % N := by
    have e : (s - r : ZMod N) = (s - p) - (r - p) := by ring
    rw [e, val_sub']
  have hv1 := ZMod.val_lt (q - p)
  have hv2 := ZMod.val_lt (r - p)
  have hv3 := ZMod.val_lt (s - p)
  by_cases hcase : (r - p).val ≤ (s - p).val
  · have hsr' : (s - r).val = (s - p).val - (r - p).val := by
      rw [hsr]
      have h1 : (s - p).val + N - (r - p).val = ((s - p).val - (r - p).val) + N := by
        omega
      rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [hpr', hsr', hqr]
    constructor <;> intro h <;> omega
  · have hsr' : (s - r).val = (s - p).val + N - (r - p).val := by
      rw [hsr, Nat.mod_eq_of_lt (by omega)]
    rw [hpr', hsr', hqr]
    constructor <;> intro h <;> omega

/-- A point different from `p` and `q` lies on one of the two open arcs
determined by them. -/
theorem sbtw_total' {N : ℕ} [NeZero N] {p q : ZMod N} (hpq : p ≠ q) {s : ZMod N}
    (hsp : s ≠ p) (hsq : s ≠ q) : sbtw p s q ∨ sbtw q s p := by
  rw [sbtw_val hsp.symm, sbtw_val hsq.symm]
  have hsq' : (s - q).val = ((s - p).val + N - (q - p).val) % N := by
    have e : (s - q : ZMod N) = (s - p) - (q - p) := by ring
    rw [e, val_sub']
  have hpq' : (p - q).val = N - (q - p).val := by
    have e : (p - q : ZMod N) = -(q - p) := by ring
    rw [e, val_neg'' (sub_ne_zero.mpr hpq.symm)]
  rw [hsq', hpq']
  have hv1 := ZMod.val_lt (q - p)
  have hv2 := ZMod.val_lt (s - p)
  have h1qp : 1 ≤ (q - p).val := by
    by_contra h0
    have hz : (q - p).val = 0 := by omega
    have hne : q - p ≠ 0 := sub_ne_zero.mpr hpq.symm
    apply hne
    have e := ZMod.natCast_zmod_val (q - p)
    rw [hz, Nat.cast_zero] at e
    exact e.symm
  have h1sp : 1 ≤ (s - p).val := by
    by_contra h0
    have hz : (s - p).val = 0 := by omega
    have hne : s - p ≠ 0 := sub_ne_zero.mpr hsp
    apply hne
    have e := ZMod.natCast_zmod_val (s - p)
    rw [hz, Nat.cast_zero] at e
    exact e.symm
  by_cases hcase : (s - p).val < (q - p).val
  · exact Or.inl hcase
  · right
    have h1 : (s - p).val + N - (q - p).val = ((s - p).val - (q - p).val) + N := by
      omega
    rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    omega

/-- The number of points lying strictly between `p` and `q` (in the clockwise
direction) is `(q - p).val - 1`. -/
theorem card_sbtw_arc {N : ℕ} [NeZero N] {p q : ZMod N} (hpq : p ≠ q) :
    (Finset.univ.filter (fun r : ZMod N => sbtw p r q)).card = (q - p).val - 1 := by
  have hL : 1 ≤ (q - p).val := by
    have hne : q - p ≠ 0 := sub_ne_zero.mpr hpq.symm
    by_contra h0
    have hz : (q - p).val = 0 := by omega
    apply hne
    have e := ZMod.natCast_zmod_val (q - p)
    rw [hz, Nat.cast_zero] at e
    exact e.symm
  have himg : (Finset.univ.filter (fun r : ZMod N => sbtw p r q)).image (fun r => r - p) =
      Finset.univ.filter (fun u : ZMod N => sbtw 0 u (q - p)) := by
    ext u
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨r, hr, rfl⟩
      have hne := (sbtw_ne' hr).1
      have h2 := (sbtw_add (-p) hne).2 hr
      rwa [show p + -p = 0 from add_neg_cancel p, ← sub_eq_add_neg r p,
        ← sub_eq_add_neg q p] at h2
    · intro hu
      refine ⟨u + p, ?_, by ring⟩
      have hne := (sbtw_ne' hu).1
      have h2 := (sbtw_add p hne).2 hu
      rwa [zero_add, sub_add_cancel] at h2
  have hcard_img : (Finset.univ.filter (fun r : ZMod N => sbtw p r q)).card =
      (Finset.univ.filter (fun u : ZMod N => sbtw 0 u (q - p))).card := by
    rw [← himg, Finset.card_image_of_injective _ (fun x y h => by
      have h2 := congrArg (· + p) h
      simpa using h2)]
  rw [hcard_img]
  have hfilter : (Finset.univ.filter fun u : ZMod N => sbtw 0 u (q - p)) =
      Finset.univ.filter (fun u : ZMod N => u.val < (q - p).val ∧ u ≠ 0) := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      have hne := (sbtw_ne' h).1
      rw [sbtw_val hne, sub_zero, sub_zero] at h
      exact ⟨h, hne.symm⟩
    · rintro ⟨h, hu⟩
      rw [sbtw_val hu.symm, sub_zero, sub_zero]
      exact h
  rw [hfilter]
  have himg2 : (Finset.univ.filter (fun u : ZMod N =>
        u.val < (q - p).val ∧ u ≠ 0)).image ZMod.val =
      (Finset.range N).filter (fun i => i < (q - p).val ∧ i ≠ 0) := by
    ext i
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_range]
    constructor
    · rintro ⟨u, ⟨hu, hu0⟩, rfl⟩
      have huv := ZMod.val_lt u
      have h0 : u.val ≠ 0 := by
        intro h0
        apply hu0
        have e := ZMod.natCast_zmod_val u
        rw [h0, Nat.cast_zero] at e
        exact e.symm
      exact ⟨huv, hu, h0⟩
    · rintro ⟨hiN, hiL, hi0⟩
      refine ⟨(i : ZMod N), ⟨by rw [ZMod.val_natCast, Nat.mod_eq_of_lt hiN]; exact hiL,
        ?_⟩, by rw [ZMod.val_natCast, Nat.mod_eq_of_lt hiN]⟩
      intro h0
      apply hi0
      have e := congrArg ZMod.val h0
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt hiN, ZMod.val_zero] at e
      exact e
  have hcard2 : (Finset.univ.filter (fun u : ZMod N =>
        u.val < (q - p).val ∧ u ≠ 0)).card =
      ((Finset.range N).filter (fun i => i < (q - p).val ∧ i ≠ 0)).card := by
    rw [← himg2, Finset.card_image_of_injective _ (ZMod.val_injective N)]
  rw [hcard2]
  have hsub : (Finset.range N).filter (fun i => i < (q - p).val ∧ i ≠ 0) =
      (Finset.range ((q - p).val)).filter (fun i => i ≠ 0) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨-, hiL, hi0⟩
      exact ⟨hiL, hi0⟩
    · rintro ⟨hiL, hi0⟩
      have hLN : (q - p).val ≤ N := le_of_lt (ZMod.val_lt _)
      exact ⟨by omega, hiL, hi0⟩
  rw [hsub]
  have herase : (Finset.range ((q - p).val)).filter (fun i => i ≠ 0) =
      (Finset.range ((q - p).val)).erase 0 := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_range, and_comm]
  rw [herase, Finset.card_erase_of_mem (Finset.mem_range.2 (by omega : 0 < (q - p).val)),
    Finset.card_range]

/-- If an aligned, vertex-disjoint, covering chord family has exactly two
degenerate chords `{p, p}` and `{q, q}` (with `p ≠ q`), then the two are
antipodal: `q + q = p + p`. Every non-degenerate chord separates `p` from `q`
(a degenerate chord cannot separate anything), so the partner map is an
involution swapping the two open arcs from `p` to `q` and from `q` to `p`;
the two arcs therefore have the same number of points. -/
theorem two_degenerate_sum_eq {N : ℕ} [NeZero N] {F : Finset (Chord N)}
    (hdj : ChordDisjoint F) (hal : ChordAligned F)
    (hcov : ∀ p : ZMod N, ∃ A ∈ F, p = A.1 ∨ p = A.2)
    {p q : ZMod N} (hpq : p ≠ q) (hpF : (p, p) ∈ F) (hqF : (q, q) ∈ F)
    (hdeg2 : ∀ A ∈ F, A.1 = A.2 → A = (p, p) ∨ A = (q, q)) :
    q + q = p + p := by
  classical
  -- the unique chord through a point
  have huniq : ∀ (r : ZMod N) (B C : Chord N), B ∈ F → C ∈ F →
      (r = B.1 ∨ r = B.2) → (r = C.1 ∨ r = C.2) → B = C := by
    intro r B C hB hC hrB hrC
    by_contra hne
    obtain ⟨d1, d2, d3, d4⟩ := hdj B hB C hC hne
    rcases hrB with rfl | rfl <;> rcases hrC with h | h
    · exact d1 h
    · exact d2 h
    · exact d3 h
    · exact d4 h
  -- the partner map `φ`, defined via the covering chord
  set Aof : ZMod N → Chord N := fun r => Classical.choose (hcov r) with hAof
  have hAof_spec : ∀ r : ZMod N, Aof r ∈ F ∧ (r = (Aof r).1 ∨ r = (Aof r).2) :=
    fun r => Classical.choose_spec (hcov r)
  set φ : ZMod N → ZMod N := fun r =>
    if (Aof r).1 = r then (Aof r).2 else (Aof r).1 with hφ
  have hφeq : ∀ r, φ r = if (Aof r).1 = r then (Aof r).2 else (Aof r).1 :=
    fun r => by rw [hφ]
  have hmem : ∀ r, Aof r ∈ F := fun r => (hAof_spec r).1
  have hcovr : ∀ r, r = (Aof r).1 ∨ r = (Aof r).2 := fun r => (hAof_spec r).2
  have hφspec : ∀ r, Aof r = (r, φ r) ∨ Aof r = (φ r, r) := by
    intro r
    rw [hφeq]
    by_cases h1 : (Aof r).1 = r
    · rw [if_pos h1]
      exact Or.inl (Prod.ext h1 rfl)
    · rw [if_neg h1]
      have h2 : r = (Aof r).2 := by
        rcases hcovr r with h2 | h2
        · exact absurd h2.symm h1
        · exact h2
      exact Or.inr (Prod.ext rfl h2.symm)
  have hAofφ : ∀ r, Aof (φ r) = Aof r := by
    intro r
    apply huniq (φ r) _ _ (hmem (φ r)) (hmem r) (hAof_spec (φ r)).2
    rw [hφeq]
    by_cases h1 : (Aof r).1 = r
    · rw [if_pos h1]
      exact Or.inr rfl
    · rw [if_neg h1]
      exact Or.inl rfl
  have hφinv : ∀ r, φ (φ r) = r := by
    intro r
    rcases hφspec r with h | h <;> rcases hφspec (φ r) with h2 | h2
    · rw [hAofφ r, h] at h2
      exact (Prod.mk.inj h2).2.symm.trans (Prod.mk.inj h2).1.symm
    · rw [hAofφ r, h] at h2
      exact (Prod.mk.inj h2).1.symm
    · rw [hAofφ r, h] at h2
      exact (Prod.mk.inj h2).2.symm
    · rw [hAofφ r, h] at h2
      exact (Prod.mk.inj h2).1.symm.trans (Prod.mk.inj h2).2.symm
  -- the key arc-swapping property, parametric in the order of the two points
  have key : ∀ {p' q' : ZMod N}, p' ≠ q' → (p', p') ∈ F → (q', q') ∈ F →
      (∀ A ∈ F, A.1 = A.2 → A = (p', p') ∨ A = (q', q')) →
      ∀ r : ZMod N, sbtw p' r q' → sbtw q' (φ r) p' := by
    intro p' q' hp'q' hp'F hq'F hdeg2' r hr
    have hp'q'F : (p', p') ≠ (q', q') := fun h => hp'q' (Prod.mk.inj h).1
    -- separation by every non-degenerate chord
    have hsep : ∀ A ∈ F, A.1 ≠ A.2 →
        (sbtw A.1 p' A.2 ∧ ¬ sbtw A.1 q' A.2) ∨ (¬ sbtw A.1 p' A.2 ∧ sbtw A.1 q' A.2) := by
      intro A hA hAd
      have h1 : (p', p') ≠ A := by
        intro h
        rw [← h] at hAd
        exact hAd rfl
      have h2 : (q', q') ≠ A := by
        intro h
        rw [← h] at hAd
        exact hAd rfl
      obtain h | h | h := hal (p', p') hp'F (q', q') hq'F A hA hp'q'F h2 h1
      · rcases h with ⟨a, -, -, -⟩ | ⟨-, -, a, -⟩ <;> exact absurd a sbtw_irrefl_left_right
      · rcases h with ⟨a, -, -, -⟩ | ⟨-, -, a, -⟩ <;> exact absurd a sbtw_irrefl_left_right
      · rcases h with ⟨a, -, c, -⟩ | ⟨a, -, c, -⟩
        · exact Or.inl ⟨a, c⟩
        · exact Or.inr ⟨a, c⟩
    have hdegφ : (Aof r).1 ≠ (Aof r).2 := by
      have hpr := (sbtw_ne' hr).1
      have hrq := (sbtw_ne' hr).2.1
      intro hd
      rcases hdeg2' _ (hmem r) hd with h | h
      · rcases hcovr r with h1 | h1 <;> rw [h] at h1
        · exact hpr h1.symm
        · exact hpr h1.symm
      · rcases hcovr r with h1 | h1 <;> rw [h] at h1
        · exact hrq h1
        · exact hrq h1
    have hφpq' : φ r ≠ p' ∧ φ r ≠ q' := by
      have h1 : Aof r ≠ (p', p') := by
        intro h
        rw [h] at hdegφ
        exact hdegφ rfl
      have h2 : Aof r ≠ (q', q') := by
        intro h
        rw [h] at hdegφ
        exact hdegφ rfl
      obtain ⟨e1, -, e3, -⟩ := hdj _ (hmem r) _ hp'F h1
      obtain ⟨f1, -, f3, -⟩ := hdj _ (hmem r) _ hq'F h2
      rw [hφeq]
      by_cases h1' : (Aof r).1 = r
      · rw [if_pos h1']
        exact ⟨e3, f3⟩
      · rw [if_neg h1']
        exact ⟨e1, f1⟩
    have hse := hsep _ (hmem r) hdegφ
    rcases sbtw_total' hp'q' hφpq'.1 hφpq'.2 with hs | hs
    · -- `φ r` on the same arc as `r`: contradiction via `sbtw_same_arc`
      rcases hφspec r with hA | hA
      · rw [hA] at hse
        have hss : sbtw r p' (φ r) ↔ sbtw r q' (φ r) := sbtw_same_arc hr hs
        rcases hse with ⟨a1, a2⟩ | ⟨a1, a2⟩
        · exact absurd (hss.1 a1) a2
        · exact absurd (hss.2 a2) a1
      · rw [hA] at hse
        have hss : sbtw (φ r) p' r ↔ sbtw (φ r) q' r := sbtw_same_arc hs hr
        rcases hse with ⟨a1, a2⟩ | ⟨a1, a2⟩
        · exact absurd (hss.1 a1) a2
        · exact absurd (hss.2 a2) a1
    · exact hs
  -- the two arcs are swapped by `φ`, hence have the same cardinality
  set arc1 := Finset.univ.filter (fun r : ZMod N => sbtw p r q) with harc1
  set arc2 := Finset.univ.filter (fun r : ZMod N => sbtw q r p) with harc2
  have hmap1 : ∀ r ∈ arc1, φ r ∈ arc2 := by
    intro r hr
    rw [harc1, Finset.mem_filter] at hr
    rw [harc2, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, key hpq hpF hqF hdeg2 r hr.2⟩
  have hmap2 : ∀ r ∈ arc2, φ r ∈ arc1 := by
    intro r hr
    rw [harc2, Finset.mem_filter] at hr
    rw [harc1, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, key hpq.symm hqF hpF
      (fun A hA hd => (hdeg2 A hA hd).symm) r hr.2⟩
  have hinj1 : Set.InjOn φ arc1 := by
    intro a _ b _ hab
    have h2 := congrArg φ hab
    rw [hφinv, hφinv] at h2
    exact h2
  have hinj2 : Set.InjOn φ arc2 := by
    intro a _ b _ hab
    have h2 := congrArg φ hab
    rw [hφinv, hφinv] at h2
    exact h2
  have hcard_eq : arc1.card = arc2.card :=
    le_antisymm (Finset.card_le_card_of_injOn φ hmap1 hinj1)
      (Finset.card_le_card_of_injOn φ hmap2 hinj2)
  have hcard1 : arc1.card = (q - p).val - 1 := by
    rw [harc1]
    exact card_sbtw_arc hpq
  have hcard2 : arc2.card = (p - q).val - 1 := by
    rw [harc2]
    exact card_sbtw_arc hpq.symm
  have hL1 : 1 ≤ (q - p).val := by
    by_contra h0
    have hz : (q - p).val = 0 := by omega
    have hne : q - p ≠ 0 := sub_ne_zero.mpr hpq.symm
    apply hne
    have e := ZMod.natCast_zmod_val (q - p)
    rw [hz, Nat.cast_zero] at e
    exact e.symm
  have hL2 : 1 ≤ (p - q).val := by
    by_contra h0
    have hz : (p - q).val = 0 := by omega
    have hne : p - q ≠ 0 := sub_ne_zero.mpr hpq
    apply hne
    have e := ZMod.natCast_zmod_val (p - q)
    rw [hz, Nat.cast_zero] at e
    exact e.symm
  rw [hcard_eq] at hcard1
  have hveq : (q - p).val = (p - q).val := by omega
  have hpvq : (p - q).val = N - (q - p).val := by
    have e : (p - q : ZMod N) = -(q - p) := by ring
    rw [e, val_neg'' (sub_ne_zero.mpr hpq.symm)]
  have hv := ZMod.val_lt (q - p)
  have h2v : 2 * (q - p).val = N := by omega
  have h2z : (2 : ZMod N) * (q - p) = 0 := by
    rw [show (2 : ZMod N) * (q - p) = ((2 * (q - p).val : ℕ) : ZMod N) from by
      rw [Nat.cast_mul, Nat.cast_two, ZMod.natCast_zmod_val]]
    rw [h2v, ZMod.natCast_self]
  have h2qp : (2 : ZMod N) * q = 2 * p := by linear_combination h2z
  linear_combination h2qp


/-! ## Two-degenerate strengthening of the structure theorem

The hypothesis “at most one degenerate chord” of `const_sum_of_aligned` is
weakened to an antipodal condition: the family may contain up to two degenerate
chords, but then their endpoint sums agree (`A.1 + A.1 = B.1 + B.1`, i.e. the two
degenerate chords sit at antipodal points). The conclusion is unchanged: the whole
family has constant endpoint-sum (`const_sum_of_aligned_two`).

The proof reuses the peel/boundary machinery with three patched spots:
* `peel_step_two`: the two-consecutive-degenerates subcase is closed by a direct
  alignment argument (`not_aligned_of_two_deg`) instead of the uniqueness of the
  degenerate chord — two degenerate chords can never be separated by a third
  chord, and `{Rt, L}` does not separate them since both points lie on the same
  arc;
* `boundary_analysis_two`: two consecutive degenerate points `P + 1, P + 2` are
  excluded since antipodal points would force `2 = 0` in `ZMod (m + 1)`;
* `boundary_data_two`: the all-degenerate case is no longer contradictory, so the
  existence of a non-degenerate chord is assumed instead (the all-degenerate case
  is handled directly in `const_sum_of_aligned_two`, where coverage forces
  `m + 1 ≤ 2`). -/

/-- Two degenerate chords whose points both lie strictly between `Rt` and `L`,
together with any chord `{Rt, L}`, form a non-aligned triple: a degenerate chord
cannot separate anything (strict betweenness with equal outer points is
impossible), and `{Rt, L}` does not separate the two degenerate chords since both
points lie on the same arc. -/
theorem not_aligned_of_two_deg {m : ℕ} {C0 B C : Chord (m + 1)} {L Rt a b : ZMod (m + 1)}
    (hC0 : (C0.1 = Rt ∧ C0.2 = L) ∨ (C0.1 = L ∧ C0.2 = Rt))
    (hB : B.1 = a ∧ B.2 = a) (hC : C.1 = b ∧ C.2 = b)
    (ha : sbtw Rt a L) (hb : sbtw Rt b L)
    (halign : ChordSep C0 B C ∨ ChordSep B C0 C ∨ ChordSep C C0 B) : False := by
  have hane := sbtw_ne ha
  have hbne := sbtw_ne hb
  have ha' : ¬ sbtw L a Rt := (sbtw_not_reverse hane.1 hane.2.1 hane.2.2.symm).1 ha
  have hb' : ¬ sbtw L b Rt := (sbtw_not_reverse hbne.1 hbne.2.1 hbne.2.2.symm).1 hb
  rcases hC0 with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;>
    simp only [ChordSep] at halign <;>
    rw [e1, e2, hB.1, hB.2, hC.1, hC.2] at halign
  · -- `C0 = (Rt, L)`
    rcases halign with (⟨-, -, h3, -⟩ | ⟨h1, -, -, -⟩) |
      (⟨h1, -, -, -⟩ | ⟨-, -, h3, -⟩) | (⟨h1, -, -, -⟩ | ⟨-, -, h3, -⟩)
    · exact h3 hb
    · exact h1 ha
    · exact sbtw_irrefl_left_right h1
    · exact sbtw_irrefl_left_right h3
    · exact sbtw_irrefl_left_right h1
    · exact sbtw_irrefl_left_right h3
  · -- `C0 = (L, Rt)`
    rcases halign with (⟨h1, -, -, -⟩ | ⟨-, -, h3, -⟩) |
      (⟨h1, -, -, -⟩ | ⟨-, -, h3, -⟩) | (⟨h1, -, -, -⟩ | ⟨-, -, h3, -⟩)
    · exact ha' h1
    · exact hb' h3
    · exact sbtw_irrefl_left_right h1
    · exact sbtw_irrefl_left_right h3
    · exact sbtw_irrefl_left_right h1
    · exact sbtw_irrefl_left_right h3

/-- The peeling step (two-degenerate version): if the arc has at least two
uncovered points, the chord through the next point on the `V` side is forced to be
`{V+i, U-i}`, extending the invariant. The only difference from `peel_step` is the
two-consecutive-degenerates subcase, which is now closed by a direct alignment
argument (`not_aligned_of_two_deg`) instead of the uniqueness of the degenerate
chord. -/
theorem peel_step_two {m : ℕ} {F : Finset (Chord (m + 1))}
    (hnc : ChordNonCrossing F) (hdj : ChordDisjoint F) (hal : ChordAligned F)
    (hcov : ∀ p : ZMod (m + 1), ∃ A ∈ F, p = A.1 ∨ p = A.2)
    (_hdeg : ∀ A ∈ F, ∀ B ∈ F, A.1 = A.2 → B.1 = B.2 → A = B ∨ A.1 + A.1 = B.1 + B.1)
    {U V R : ZMod (m + 1)} {i : ℕ} (hi : 1 ≤ i) (hUV1 : 1 ≤ (V - U).val)
    (hroom : (V - U).val + 2 * i ≤ m) (hinv : PeelInv F U V R i) :
    PeelInv F U V R (i + 1) := by
  obtain ⟨hI1, hI2, hI3, hI4, hI5, hI6⟩ := hinv
  set s := (V - U).val with hs
  set Rt : ZMod (m + 1) := V + (i : ZMod (m + 1)) - 1 with hRt
  set L : ZMod (m + 1) := U - (i : ZMod (m + 1)) + 1 with hL
  set a : ZMod (m + 1) := V + (i : ZMod (m + 1)) with ha
  set b : ZMod (m + 1) := U - (i : ZMod (m + 1)) with hb
  have hm : 3 ≤ m := by omega
  -- the previous chord `c_{i-1}` has endpoints `{Rt, L}`
  obtain ⟨C0, hC0F, hC0e⟩ := hI1 (i - 1) (by omega)
  have eRt : V + ((i - 1 : ℕ) : ZMod (m + 1)) = Rt := by
    rw [hRt, ha, Nat.cast_sub hi, Nat.cast_one]; ring
  have eL : U - ((i - 1 : ℕ) : ZMod (m + 1)) = L := by
    rw [hL, hb, Nat.cast_sub hi, Nat.cast_one]; ring
  rw [eRt, eL] at hC0e
  -- val identities
  have hcast : ∀ k : ℕ, (V - U) + (k : ZMod (m + 1)) = ((s + k : ℕ) : ZMod (m + 1)) := by
    intro k
    have e : ((s : ZMod (m + 1))) = V - U := by rw [hs, ZMod.natCast_zmod_val]
    rw [Nat.cast_add, e]
  have hRtL : (Rt - L).val = s + 2 * i - 2 := by
    have e : Rt - L = (V - U) + ((2 * i - 2 : ℕ) : ZMod (m + 1)) := by
      rw [hRt, hL, ha, hb, Nat.cast_sub (by omega : 2 ≤ 2 * i)]; push_cast; ring
    rw [e, hcast, val_natCast_of_lt (by omega)]; omega
  have haRt : (a - Rt).val = 1 := by
    have e : a - Rt = 1 := by rw [hRt]; ring
    rw [e, val_one' (by omega : 1 ≤ m)]
  have hbRt : (b - Rt).val = m + 1 - (s + 2 * i - 1) := by
    have e : b - Rt = -(((s + (2 * i - 1) : ℕ)) : ZMod (m + 1)) := by
      have e1 : (V - U) + ((2 * i - 1 : ℕ) : ZMod (m + 1)) = ((s + (2 * i - 1) : ℕ) : ZMod (m + 1)) := hcast _
      have e2 : b - Rt = -((V - U) + ((2 * i - 1 : ℕ) : ZMod (m + 1))) := by
        rw [hb, hRt, ha, Nat.cast_sub (by omega : 1 ≤ 2 * i)]; push_cast; ring
      rw [e2, e1]
    rw [e, val_neg_natCast (by omega : 1 ≤ s + (2 * i - 1)) (by omega : s + (2 * i - 1) ≤ m)]; omega
  have hLRt : (L - Rt).val = m + 1 - (s + 2 * i - 2) := by
    have e : L - Rt = -(((s + (2 * i - 2) : ℕ)) : ZMod (m + 1)) := by
      have e1 : Rt - L = ((s + (2 * i - 2) : ℕ) : ZMod (m + 1)) := by
        have e2 : Rt - L = (V - U) + ((2 * i - 2 : ℕ) : ZMod (m + 1)) := by
          rw [hRt, hL, ha, hb, Nat.cast_sub (by omega : 2 ≤ 2 * i)]; push_cast; ring
        rw [e2, hcast]
      rw [show L - Rt = -(Rt - L) from by ring, e1]
    rw [e, val_neg_natCast (by omega : 1 ≤ s + (2 * i - 2)) (by omega : s + (2 * i - 2) ≤ m)]; omega
  have haL : (a - L).val = s + 2 * i - 1 := by
    have e : a - L = (V - U) + ((2 * i - 1 : ℕ) : ZMod (m + 1)) := by
      rw [ha, hL, hb, Nat.cast_sub (by omega : 1 ≤ 2 * i)]; push_cast; ring
    rw [e, hcast, val_natCast_of_lt (by omega)]; omega
  have hbL : (b - L).val = m := by
    have e : b - L = -1 := by rw [hL]; ring
    rw [e]
    have e1 : (-1 : ZMod (m + 1)) = -((1 : ℕ) : ZMod (m + 1)) := by rw [Nat.cast_one]
    rw [e1, val_neg_natCast (le_refl 1) (by omega : 1 ≤ m)]
    omega
  have hab : (a - b).val = s + 2 * i := by
    have e : a - b = (V - U) + ((2 * i : ℕ) : ZMod (m + 1)) := by rw [ha, hb]; push_cast; ring
    rw [e, hcast, val_natCast_of_lt (by omega)]
  -- distinctness
  have LRt : L ≠ Rt := by
    intro he; rw [he, sub_self] at hRtL; simp at hRtL; omega
  have aRt : a ≠ Rt := by
    intro he; rw [he, sub_self] at haRt; simp at haRt
  have bRt : b ≠ Rt := by
    intro he; rw [he, sub_self] at hbRt; simp at hbRt; omega
  have aL : a ≠ L := by
    intro he; rw [he, sub_self] at haL; simp at haL; omega
  have bL : b ≠ L := by
    intro he; rw [he, sub_self] at hbL; simp at hbL; omega
  have ab : a ≠ b := by
    intro he; rw [he, sub_self] at hab; simp at hab; omega
  -- arc membership of the fresh points
  have ha_far : sbtw Rt a L := by
    rw [sbtw_val aRt.symm, haRt, hLRt]; omega
  have hb_far : sbtw Rt b L := by
    rw [sbtw_val bRt.symm, hbRt, hLRt]; omega
  have ha_narc : ¬ btw L a Rt := by
    rw [btw_val LRt, haL, hRtL]; omega
  have hb_narc : ¬ btw L b Rt := by
    rw [btw_val LRt, hbL, hRtL]; omega
  -- cover `a`
  obtain ⟨B, hBF, hBa⟩ := hcov a
  have hBC0 : C0 ≠ B := by
    intro he
    rw [← he] at hBa
    rcases hC0e with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2] at hBa
    · rcases hBa with h | h
      · exact aRt h
      · exact aL h
    · rcases hBa with h | h
      · exact aL h
      · exact aRt h
  obtain ⟨q, hBq⟩ : ∃ q, (B.1 = a ∧ B.2 = q) ∨ (B.1 = q ∧ B.2 = a) := by
    rcases hBa with h | h
    · exact ⟨B.2, Or.inl ⟨h.symm, rfl⟩⟩
    · exact ⟨B.1, Or.inr ⟨rfl, h.symm⟩⟩
  have hq_far : sbtw Rt q L := far_transfer hnc hdj hC0F hBF hBC0 hC0e hBq LRt ha_far
  have hqne := sbtw_ne hq_far
  rw [sbtw_val hqne.1, hLRt] at hq_far
  -- `hq_far : (q - Rt).val < m + 1 - (s + 2*i - 2)`
  by_cases hqa : q = a
  · -- `B` degenerate (impossible, via the alignment triple)
    have hBeq : B.1 = a ∧ B.2 = a := by
      rcases hBq with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · exact ⟨e1, by rw [e2, hqa]⟩
      · exact ⟨by rw [e1, hqa], e2⟩
    obtain ⟨C, hCF, hCb⟩ := hcov b
    have hCC0 : C0 ≠ C := by
      intro he
      rw [← he] at hCb
      rcases hC0e with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2] at hCb
      · rcases hCb with h | h
        · exact bRt h
        · exact bL h
      · rcases hCb with h | h
        · exact bL h
        · exact bRt h
    have hCB : B ≠ C := by
      intro he
      rw [← he] at hCb
      rcases hCb with h | h
      · exact ab (by rw [h, hBeq.1])
      · exact ab (by rw [h, hBeq.2])
    by_cases hCdeg : C.1 = C.2
    · -- `B` and `C` are both degenerate: no chord can separate two degenerate
      -- chords (strict betweenness with equal outer points is impossible), and
      -- `{Rt, L}` does not separate them since `a` and `b` lie on the same arc,
      -- so the triple `(C0, B, C)` is not aligned
      have hCeq : C.1 = b ∧ C.2 = b := by
        rcases hCb with h | h
        · exact ⟨h.symm, (hCdeg ▸ h).symm⟩
        · exact ⟨(hCdeg.symm ▸ h).symm, h.symm⟩
      exact (not_aligned_of_two_deg hC0e hBeq hCeq ha_far hb_far
        (hal C0 hC0F B hBF C hCF hBC0 hCB hCC0)).elim
    · obtain ⟨r, hCr⟩ : ∃ r, (C.1 = b ∧ C.2 = r) ∨ (C.1 = r ∧ C.2 = b) := by
        rcases hCb with h | h
        · exact ⟨C.2, Or.inl ⟨h.symm, rfl⟩⟩
        · exact ⟨C.1, Or.inr ⟨rfl, h.symm⟩⟩
      have hr : r ≠ b := by
        rcases hCr with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · intro he; exact hCdeg (by rw [e1, e2, he])
        · intro he; exact hCdeg (by rw [e1, e2, ← he])
      have hr_far : sbtw Rt r L := far_transfer hnc hdj hC0F hCF hCC0 hC0e hCr LRt hb_far
      have hrne := sbtw_ne hr_far
      rw [sbtw_val hrne.1, hLRt] at hr_far
      have hra : r ≠ a := by
        have hd := hdj B hBF C hCF hCB
        rcases hCr with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2, hBeq.1, hBeq.2] at hd
        · exact hd.2.2.2.symm
        · exact hd.2.2.1.symm
      have hvr0 : 1 ≤ (r - Rt).val := by
        rcases Nat.eq_zero_or_pos (r - Rt).val with hz | hz
        · exfalso; apply hrne.1
          have e : r - Rt = 0 := by
            have e2 := ZMod.natCast_zmod_val (r - Rt)
            rw [hz, Nat.cast_zero] at e2
            exact e2.symm
          rw [sub_eq_zero] at e; exact e.symm
        · exact hz
      have hvr1 : 1 < (r - Rt).val := by
        rcases eq_or_ne (r - Rt).val 1 with hz | hz
        · exfalso; apply hra
          have e : r - Rt = a - Rt := ZMod.val_injective _ (by rw [hz, haRt])
          exact sub_left_injective e
        · omega
      have hvr2 : (r - Rt).val < (b - Rt).val := by
        have hne : (r - Rt).val ≠ (b - Rt).val := fun hz => hr (sub_left_injective (ZMod.val_injective _ hz))
        omega
      have hb_far' : (b - Rt).val < (L - Rt).val := by
        rw [sbtw_val bRt.symm] at hb_far; exact hb_far
      exact (not_aligned_of_chain_rel_degB hC0e hBeq hCr haRt hvr1 hvr2 hb_far'
        (hal C0 hC0F B hBF C hCF hBC0 hCB hCC0)).elim
  · by_cases hqb : q = b
    · -- success: `B = {a, b}` is the new chord `c_i`
      rw [hqb] at hBq
      refine ⟨?_, ?_, ?_, hI4, ?_, by omega⟩
      · intro j hj
        rcases eq_or_lt_of_le (by omega : j ≤ i) with hje | hje
        · rw [hje]
          exact ⟨B, hBF, by rw [← ha, ← hb]; exact hBq⟩
        · exact hI1 j hje
      · intro p hp
        have e1 : U - ((i + 1 : ℕ) : ZMod (m + 1)) + 1 = b := by
          rw [hb, Nat.cast_add, Nat.cast_one]; ring
        have e2 : V + ((i + 1 : ℕ) : ZMod (m + 1)) - 1 = a := by
          rw [ha, Nat.cast_add, Nat.cast_one]; ring
        rw [e1, e2] at hp
        rcases btw_eq_or_sbtw hp ab.symm with hpb | hpa | hp'
        · exact Or.inr ⟨i, by omega, Or.inr (by rw [hpb, hb])⟩
        · exact Or.inr ⟨i, by omega, Or.inl (by rw [hpa, ha])⟩
        · -- `p` strictly between `b` and `a`: in the old arc
          have hpne := sbtw_ne hp'
          have hpL : btw L p Rt := by
            rw [btw_val LRt]
            rw [sbtw_val hpne.1, hab] at hp'
            have hpb1 : 1 ≤ (p - b).val := by
              rcases Nat.eq_zero_or_pos (p - b).val with hz | hz
              · exfalso; apply hpne.1
                have e : p - b = 0 := by
                  have e2 := ZMod.natCast_zmod_val (p - b)
                  rw [hz, Nat.cast_zero] at e2
                  exact e2.symm
                rw [sub_eq_zero] at e; exact e.symm
              · exact hz
            have e3 : p - L = (p - b) - 1 := by rw [hL]; ring
            have e4 : (p - L).val = (p - b).val - 1 := by
              rw [e3]
              have e5 : (p - b) - 1 = (((p - b).val - 1 : ℕ) : ZMod (m + 1)) := by
                rw [Nat.cast_sub hpb1, Nat.cast_one, ZMod.natCast_zmod_val]
              rw [e5, val_natCast_of_lt (by have := ZMod.val_lt (p - b); omega)]
            rw [e4, hRtL]; omega
          rcases hI2 p hpL with hpR | ⟨j, hj, hjp⟩
          · exact Or.inl hpR
          · exact Or.inr ⟨j, by omega, hjp⟩
      · intro j hj hRR
        rcases eq_or_lt_of_le (by omega : j ≤ i) with hje | hje
        · rw [hje]
          have haR : a ≠ R := by
            intro he
            rw [he] at ha_narc
            exact ha_narc (by rw [← he] at hI5 ⊢; exact hI5)
          have hbR : b ≠ R := by
            intro he
            rw [he] at hb_narc
            exact hb_narc (by rw [← he] at hI5 ⊢; exact hI5)
          rw [← ha]
          exact ⟨haR, by rw [← hb]; exact hbR⟩
        · exact hI3 j hje hRR
      · have e1 : U - ((i + 1 : ℕ) : ZMod (m + 1)) + 1 = b := by
          rw [hb, Nat.cast_add, Nat.cast_one]; ring
        have e2 : V + ((i + 1 : ℕ) : ZMod (m + 1)) - 1 = a := by
          rw [ha, Nat.cast_add, Nat.cast_one]; ring
        rw [e1, e2, btw_val ab.symm, hab]
        have hRL : (R - L).val ≤ s + 2 * i - 2 := by
          rw [btw_val LRt, hRtL] at hI5; exact hI5
        have e3 : R - b = (R - L) + 1 := by rw [hL]; ring
        have e4 : (R - b).val = (R - L).val + 1 := by
          rw [e3]
          have e5 : (R - L) + 1 = (((R - L).val + 1 : ℕ) : ZMod (m + 1)) := by
            have e6 := ZMod.natCast_zmod_val (R - L)
            rw [Nat.cast_add, Nat.cast_one, e6]
          rw [e5, val_natCast_of_lt (by have := ZMod.val_lt (R - L); omega)]
        rw [e4]; omega
    · -- the generic case is impossible (alignment triple)
      obtain ⟨C, hCF, hCb⟩ := hcov b
      have hCC0 : C0 ≠ C := by
        intro he
        rw [← he] at hCb
        rcases hC0e with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2] at hCb
        · rcases hCb with h | h
          · exact bRt h
          · exact bL h
        · rcases hCb with h | h
          · exact bL h
          · exact bRt h
      have hCB : B ≠ C := by
        intro he
        rw [← he] at hCb
        rcases hBq with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2] at hCb
        · rcases hCb with h | h
          · exact ab h.symm
          · exact hqb h.symm
        · rcases hCb with h | h
          · exact hqb h.symm
          · exact ab h.symm
      have hvq0 : 1 ≤ (q - Rt).val := by
        rcases Nat.eq_zero_or_pos (q - Rt).val with hz | hz
        · exfalso; apply hqne.1
          have e : q - Rt = 0 := by
            have e2 := ZMod.natCast_zmod_val (q - Rt)
            rw [hz, Nat.cast_zero] at e2
            exact e2.symm
          rw [sub_eq_zero] at e; exact e.symm
        · exact hz
      have hvq1 : 1 < (q - Rt).val := by
        rcases eq_or_ne (q - Rt).val 1 with hz | hz
        · exfalso; apply hqa
          have e : q - Rt = a - Rt := ZMod.val_injective _ (by rw [hz, haRt])
          exact sub_left_injective e
        · omega
      by_cases hCdeg : C.1 = C.2
      · -- `C` degenerate: impossible
        have hCeq : C.1 = b ∧ C.2 = b := by
          rcases hCb with h | h
          · exact ⟨h.symm, (hCdeg ▸ h).symm⟩
          · exact ⟨(hCdeg.symm ▸ h).symm, h.symm⟩
        have hvb2 : (q - Rt).val < (b - Rt).val := by
          have hne : (q - Rt).val ≠ (b - Rt).val := fun hz => hqb (sub_left_injective (ZMod.val_injective _ hz))
          omega
        have hb_far' : (b - Rt).val < (L - Rt).val := by
          rw [sbtw_val bRt.symm] at hb_far; exact hb_far
        exact (not_aligned_of_chain_rel_degC hC0e hBq hCeq haRt hvq1 hvb2 hb_far'
          (hal C0 hC0F B hBF C hCF hBC0 hCB hCC0)).elim
      · obtain ⟨r, hCr⟩ : ∃ r, (C.1 = b ∧ C.2 = r) ∨ (C.1 = r ∧ C.2 = b) := by
          rcases hCb with h | h
          · exact ⟨C.2, Or.inl ⟨h.symm, rfl⟩⟩
          · exact ⟨C.1, Or.inr ⟨rfl, h.symm⟩⟩
        have hr : r ≠ b := by
          rcases hCr with ⟨e1, e2⟩ | ⟨e1, e2⟩
          · intro he; exact hCdeg (by rw [e1, e2, he])
          · intro he; exact hCdeg (by rw [e1, e2, ← he])
        have hr_far : sbtw Rt r L := far_transfer hnc hdj hC0F hCF hCC0 hC0e hCr LRt hb_far
        have hrne := sbtw_ne hr_far
        rw [sbtw_val hrne.1, hLRt] at hr_far
        have hdBC := hdj B hBF C hCF hCB
        have hBC := hnc B hBF C hCF hCB
        -- value conversions relative to `Rt`
        have hid : ∀ x y : ZMod (m + 1), (x - Rt).val < (y - Rt).val →
            ((y - x).val = (y - Rt).val - (x - Rt).val) := by
          intro x y hxy
          have e : y - x = (((y - Rt).val - (x - Rt).val : ℕ) : ZMod (m + 1)) := by
            have e1 := ZMod.natCast_zmod_val (y - Rt)
            have e2 := ZMod.natCast_zmod_val (x - Rt)
            have e3 : y - x = (y - Rt) - (x - Rt) := by ring
            rw [e3, Nat.cast_sub (by omega : (x - Rt).val ≤ (y - Rt).val), e1, e2]
          rw [e, val_natCast_of_lt (by have := ZMod.val_lt (y - Rt); have := ZMod.val_lt (x - Rt); omega)]
        have hid1 : ∀ x : ZMod (m + 1), 1 ≤ (x - Rt).val →
            ((x - a).val = (x - Rt).val - 1) := by
          intro x hx
          have e : x - a = (((x - Rt).val - 1 : ℕ) : ZMod (m + 1)) := by
            have e1 := ZMod.natCast_zmod_val (x - Rt)
            have e2 : x - a = (x - Rt) - 1 := by rw [hRt]; ring
            rw [e2, Nat.cast_sub hx, Nat.cast_one, e1]
          rw [e, val_natCast_of_lt (by have := ZMod.val_lt (x - Rt); omega)]
        have hid2 : ∀ x : ZMod (m + 1), 2 ≤ (x - Rt).val →
            ((a - x).val = m + 1 - ((x - Rt).val - 1)) := by
          intro x hx
          have e : a - x = -(((x - Rt).val - 1 : ℕ) : ZMod (m + 1)) := by
            have e1 : x - a = (((x - Rt).val - 1 : ℕ) : ZMod (m + 1)) := by
              have e2 := ZMod.natCast_zmod_val (x - Rt)
              have e3 : x - a = (x - Rt) - 1 := by rw [hRt]; ring
              rw [e3, Nat.cast_sub (by omega : 1 ≤ (x - Rt).val), Nat.cast_one, e2]
            rw [show a - x = -(x - a) from by ring, e1]
          rw [e, val_neg_natCast (by omega : 1 ≤ (x - Rt).val - 1)
            (by have := ZMod.val_lt (x - Rt); omega : (x - Rt).val - 1 ≤ m)]
        have hvr0 : 1 ≤ (r - Rt).val := by
          rcases Nat.eq_zero_or_pos (r - Rt).val with hz | hz
          · exfalso; apply hrne.1
            have e : r - Rt = 0 := by
              have e2 := ZMod.natCast_zmod_val (r - Rt)
              rw [hz, Nat.cast_zero] at e2
              exact e2.symm
            rw [sub_eq_zero] at e; exact e.symm
          · exact hz
        have hra : r ≠ a := by
          rcases hBq with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rcases hCr with ⟨e3, e4⟩ | ⟨e3, e4⟩ <;>
            rw [e1, e2, e3, e4] at hdBC
          · exact hdBC.2.1.symm
          · exact hdBC.1.symm
          · exact hdBC.2.2.2.symm
          · exact hdBC.2.2.1.symm
        have hrq : r ≠ q := by
          rcases hBq with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rcases hCr with ⟨e3, e4⟩ | ⟨e3, e4⟩ <;>
            rw [e1, e2, e3, e4] at hdBC
          · exact hdBC.2.2.2.symm
          · exact hdBC.2.2.1.symm
          · exact hdBC.2.1.symm
          · exact hdBC.1.symm
        have hvr1 : (r - Rt).val ≠ 1 := by
          intro hz
          apply hra
          have e : r - Rt = a - Rt := ZMod.val_injective _ (by rw [hz, haRt])
          exact sub_left_injective e
        have hvrq : (r - Rt).val ≠ (q - Rt).val := fun hz => hrq (sub_left_injective (ZMod.val_injective _ hz))
        -- `sbtw a b q` and `sbtw a r q`
        have hba_conv : (b - a).val = m + 1 - (s + 2 * i) := by
          have e : b - a = -(((s + 2 * i : ℕ)) : ZMod (m + 1)) := by
            have e1 : a - b = ((s + 2 * i : ℕ) : ZMod (m + 1)) := by
              have e2 : a - b = (V - U) + ((2 * i : ℕ) : ZMod (m + 1)) := by rw [ha, hb]; push_cast; ring
              rw [e2, hcast]
            rw [show b - a = -(a - b) from by ring, e1]
          rw [e, val_neg_natCast (by omega : 1 ≤ s + 2 * i) (by omega : s + 2 * i ≤ m)]
        -- the chain `(q - Rt).val < (r - Rt).val` from non-crossing of `B` and `C`
        have hqr : (q - Rt).val < (r - Rt).val := by
          have hvq2 : 2 ≤ (q - Rt).val := by omega
          have hvr2 : 2 ≤ (r - Rt).val := by omega
          have hvb2 : 2 ≤ (b - Rt).val := by omega
          have hqbv : (q - Rt).val < (b - Rt).val := by
            have hne : (q - Rt).val ≠ (b - Rt).val := fun hz =>
              hqb (sub_left_injective (ZMod.val_injective _ hz))
            omega
          have hTra : ∀ x y : ZMod (m + 1), 2 ≤ (x - Rt).val → 2 ≤ (y - Rt).val →
              (sbtw a x y ↔ (x - Rt).val < (y - Rt).val) := by
            intro x y hx hy
            have e1 : a - Rt = 1 := by rw [hRt]; ring
            have h1x : (1 : ZMod (m + 1)) ≠ x - Rt := by
              intro he
              rw [← he, val_one' (by omega : 1 ≤ m)] at hx
              omega
            have habx : a ≠ x := by
              intro he
              rw [← he, e1] at h1x
              exact h1x rfl
            rw [← sbtw_sub Rt habx, e1, sbtw_val h1x,
              show x - Rt - 1 = x - a from by rw [hRt]; ring,
              show y - Rt - 1 = y - a from by rw [hRt]; ring,
              hid1 x (by omega : 1 ≤ (x - Rt).val), hid1 y (by omega : 1 ≤ (y - Rt).val)]
            constructor <;> intro h' <;> omega
          have hTrq : ∀ x : ZMod (m + 1), 2 ≤ (x - Rt).val → q ≠ x →
              (sbtw q x a ↔ (q - Rt).val < (x - Rt).val) := by
            intro x hx hqx
            have h1 : q - Rt ≠ x - Rt := fun he => hqx (sub_left_injective he)
            have e1 : a - Rt = 1 := by rw [hRt]; ring
            rw [← sbtw_sub Rt hqx, e1, sbtw_val h1]
            have h2 : ((x - Rt) - (q - Rt)).val = if (q - Rt).val ≤ (x - Rt).val then
                (x - Rt).val - (q - Rt).val else (x - Rt).val + (m + 1) - (q - Rt).val := by
              have e3 : (x - Rt) - (q - Rt) =
                  (((x - Rt).val : ℕ) : ZMod (m + 1)) - (((q - Rt).val : ℕ) : ZMod (m + 1)) := by
                have e4 := ZMod.natCast_zmod_val (x - Rt)
                have e5 := ZMod.natCast_zmod_val (q - Rt)
                rw [e4, e5]
              rw [e3, val_sub_if]
              rw [val_natCast_of_lt (by have := ZMod.val_lt (x - Rt); omega : (x - Rt).val < m + 1),
                val_natCast_of_lt (by have := ZMod.val_lt (q - Rt); omega : (q - Rt).val < m + 1)]
            have h3 : (1 - (q - Rt)).val = m + 2 - (q - Rt).val := by
              have e3 : (1 : ZMod (m + 1)) - (q - Rt) = a - q := by rw [hRt]; ring
              rw [e3, hid2 q hvq1]
              omega
            have hne : (q - Rt).val ≠ (x - Rt).val := fun hz => h1 (ZMod.val_injective _ hz)
            have hlt : (q - Rt).val < m + 1 := ZMod.val_lt _
            have hlt' : (x - Rt).val < m + 1 := ZMod.val_lt _
            rw [h2, h3]
            split_ifs with hle
            · constructor <;> intro h' <;> omega
            · constructor <;> intro h' <;> omega
          rcases hBq with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rcases hCr with ⟨e3, e4⟩ | ⟨e3, e4⟩ <;>
            rw [e1, e2, e3, e4] at hBC
          · rw [hTra b q hvb2 hvq2, hTra r q hvr2 hvq2] at hBC
            omega
          · rw [hTra r q hvr2 hvq2, hTra b q hvb2 hvq2] at hBC
            omega
          · rw [hTrq b hvb2 hqb, hTrq r hvr2 hrq.symm] at hBC
            omega
          · rw [hTrq r hvr2 hrq.symm, hTrq b hvb2 hqb] at hBC
            omega
        have hrb_val : (r - Rt).val < (b - Rt).val := by
          have hne : (r - Rt).val ≠ (b - Rt).val := fun hz =>
            hr (sub_left_injective (ZMod.val_injective _ hz))
          omega
        have hb_far' : (b - Rt).val < (L - Rt).val := by
          rw [sbtw_val bRt.symm] at hb_far; exact hb_far
        exact (not_aligned_of_chain_rel hC0e hBq hCr haRt hvq1 hqr hrb_val hb_far'
          (hal C0 hC0F B hBF C hCF hBC0 hCB hCC0)).elim

/-- Finalization (two-degenerate version): once the arc covers the whole circle
(up to one point), every chord of the family has endpoint sum `U + V`. -/
theorem peel_final_two {m : ℕ} {F : Finset (Chord (m + 1))}
    (_hnc : ChordNonCrossing F) (hdj : ChordDisjoint F) (_hal : ChordAligned F)
    (_hcov : ∀ p : ZMod (m + 1), ∃ A ∈ F, p = A.1 ∨ p = A.2)
    (_hdeg : ∀ A ∈ F, ∀ B ∈ F, A.1 = A.2 → B.1 = B.2 → A = B ∨ A.1 + A.1 = B.1 + B.1)
    {U V R : ZMod (m + 1)} {i : ℕ} (hi : 1 ≤ i) (hUV1 : 1 ≤ (V - U).val)
    (hfull : m + 1 ≤ (V - U).val + 2 * i) (hinv : PeelInv F U V R i) :
    ∀ A ∈ F, A.1 + A.2 = U + V := by
  obtain ⟨hI1, hI2, hI3, hI4, hI5, hI6⟩ := hinv
  intro A hAF
  set s := (V - U).val with hs
  set L : ZMod (m + 1) := U - (i : ZMod (m + 1)) + 1 with hL
  set Rt : ZMod (m + 1) := V + (i : ZMod (m + 1)) - 1 with hRt
  have hm : 1 ≤ m := by omega
  have hcast : ∀ k : ℕ, (V - U) + (k : ZMod (m + 1)) = ((s + k : ℕ) : ZMod (m + 1)) := by
    intro k
    have e : ((s : ZMod (m + 1))) = V - U := by rw [hs, ZMod.natCast_zmod_val]
    rw [Nat.cast_add, e]
  have hRtL : (Rt - L).val = s + 2 * i - 2 := by
    have e : Rt - L = (V - U) + ((2 * i - 2 : ℕ) : ZMod (m + 1)) := by
      rw [hRt, hL, Nat.cast_sub (by omega : 2 ≤ 2 * i)]; push_cast; ring
    rw [e, hcast, val_natCast_of_lt (by omega)]; omega
  have LRt : L ≠ Rt := by
    intro he; rw [he, sub_self] at hRtL; simp at hRtL; omega
  have hLval : (L - Rt).val = m + 1 - (s + 2 * i - 2) := by
    have e : L - Rt = -(((s + (2 * i - 2) : ℕ)) : ZMod (m + 1)) := by
      have e1 : Rt - L = ((s + (2 * i - 2) : ℕ) : ZMod (m + 1)) := by
        have e2 : Rt - L = (V - U) + ((2 * i - 2 : ℕ) : ZMod (m + 1)) := by
          rw [hRt, hL, Nat.cast_sub (by omega : 2 ≤ 2 * i)]; push_cast; ring
        rw [e2, hcast]
      rw [show L - Rt = -(Rt - L) from by ring, e1]
    rw [e, val_neg_natCast (by omega : 1 ≤ s + (2 * i - 2)) (by omega : s + (2 * i - 2) ≤ m)]
    omega
  -- endpoints of the `c_j` chords lie in the arc
  have hmem : ∀ j < i, btw L (V + (j : ZMod (m + 1))) Rt ∧ btw L (U - (j : ZMod (m + 1))) Rt := by
    intro j hj
    have e1 : V + (j : ZMod (m + 1)) - L = (V - U) + ((i + j - 1 : ℕ) : ZMod (m + 1)) := by
      rw [hL, Nat.cast_sub (by omega : 1 ≤ i + j)]; push_cast; ring
    have e2 : (V + (j : ZMod (m + 1)) - L).val = s + (i + j - 1) := by
      rw [e1, hcast, val_natCast_of_lt (by omega)]
    have e3 : U - (j : ZMod (m + 1)) - L = (((i - j - 1 : ℕ)) : ZMod (m + 1)) := by
      have h1 : ((i - j - 1 : ℕ) : ZMod (m + 1)) = (i : ZMod (m + 1)) - (j : ZMod (m + 1)) - 1 := by
        have hcs : ((i - j - 1 : ℕ) : ZMod (m + 1)) = ((i - j : ℕ) : ZMod (m + 1)) - 1 :=
          Nat.cast_sub (by omega : 1 ≤ i - j)
        have hcs2 : ((i - j : ℕ) : ZMod (m + 1)) = (i : ZMod (m + 1)) - (j : ZMod (m + 1)) :=
          Nat.cast_sub (by omega : j ≤ i)
        rw [hcs, hcs2]
      rw [hL, h1]; ring
    have e4 : (U - (j : ZMod (m + 1)) - L).val = i - j - 1 := by
      rw [e3, val_natCast_of_lt (by omega)]
    rw [btw_val LRt, e2, hRtL]
    refine ⟨by omega, ?_⟩
    rw [btw_val LRt, e4, hRtL]
    omega
  -- point classification: everything is in the arc or equals `W := Rt + 1`
  set W : ZMod (m + 1) := Rt + 1 with hW
  have hclass : ∀ p : ZMod (m + 1), btw L p Rt ∨ p = W := by
    intro p
    by_cases h : btw L p Rt
    · exact Or.inl h
    · right
      have hRt_p : Rt ≠ p := by
        intro he
        exact h (by rw [← he]; exact (btw_val LRt).2 (le_refl _))
      have h2 : sbtw Rt p L :=
        of_not_not (fun hs => h ((btw_iff_not_sbtw (a := L) (b := p) (c := Rt)).2 hs))
      rw [sbtw_val hRt_p, hLval] at h2
      have h3 : (p - Rt).val = 1 := by
        have h4 : (p - Rt).val ≠ 0 := by
          intro hz
          apply hRt_p
          have e : p - Rt = 0 := by
            have e2 := ZMod.natCast_zmod_val (p - Rt)
            rw [hz, Nat.cast_zero] at e2
            exact e2.symm
          rw [sub_eq_zero] at e
          exact e.symm
        omega
      have h5 : p - Rt = 1 := ZMod.val_injective _ (by rw [h3, val_one' hm])
      have h6 : p = Rt + 1 := by linear_combination h5
      rw [h6, hW]
  -- reflection: the degenerate chord's sum is also `U + V`
  have hRefl : (R, R) ∈ F → R + R = U + V := by
    intro hRR
    have hpt : ∀ p : ZMod (m + 1), p = R ∨
        (∃ j < i, p = V + (j : ZMod (m + 1)) ∨ p = U - (j : ZMod (m + 1))) ∨ p = W := by
      intro p
      rcases hclass p with hp | hp
      · rcases hI2 p hp with hpR | hj
        · exact Or.inl hpR
        · exact Or.inr (Or.inl hj)
      · exact Or.inr (Or.inr hp)
    rcases hpt (U + V - R) with h | h | h
    · linear_combination -h
    · obtain ⟨j, hj, hjv⟩ := h
      have hRne := hI3 j hj hRR
      rcases hjv with hjv | hjv
      · exfalso; apply hRne.2; linear_combination hjv
      · exfalso; apply hRne.1; linear_combination hjv
    · -- `U + V - R = W`: then `R = U - i`, fresh, contradiction
      exfalso
      have hRi : R = U - (i : ZMod (m + 1)) := by
        have hW' : W = V + (i : ZMod (m + 1)) := by rw [hW, hRt]; ring
        rw [hW'] at h
        linear_combination -h
      by_cases hs2 : s + 2 * i = m + 2
      · have hRi2 : R = V + ((i - 1 : ℕ) : ZMod (m + 1)) := by
          have e : (V - U) + 2 * (i : ZMod (m + 1)) = 1 := by
            have h2 : ((s + 2 * i : ℕ) : ZMod (m + 1)) = 1 := by
              rw [show s + 2 * i = 1 + (m + 1) from by omega, Nat.cast_add, ZMod.natCast_self,
                Nat.cast_one]
              ring
            rw [← hcast] at h2
            rw [show (2 : ZMod (m + 1)) * (i : ZMod (m + 1)) = ((2 * i : ℕ) : ZMod (m + 1)) from by
              push_cast; ring]
            exact h2
          rw [hRi]
          have e2 : V + ((i - 1 : ℕ) : ZMod (m + 1)) = V + ((i : ZMod (m + 1)) - 1) := by
            rw [Nat.cast_sub hi, Nat.cast_one]
          rw [e2]
          linear_combination -e
        exact (hI3 (i - 1) (by omega) hRR).1 hRi2.symm
      · have hnfresh : ¬ btw L (U - (i : ZMod (m + 1))) Rt := by
          rw [btw_val LRt, hRtL]
          have e : U - (i : ZMod (m + 1)) - L = -1 := by rw [hL]; ring
          rw [e]
          have e1 : (-1 : ZMod (m + 1)) = -((1 : ℕ) : ZMod (m + 1)) := by rw [Nat.cast_one]
          rw [e1, val_neg_natCast (le_refl 1) (by omega : 1 ≤ m)]
          omega
        rw [hRi] at hI5
        exact hnfresh hI5
  -- every chord with an endpoint in the arc is a `c_j` or the degenerate chord
  have hchord : ∀ B ∈ F, ∀ p : ZMod (m + 1), (p = B.1 ∨ p = B.2) → btw L p Rt →
      (∃ j < i, (B.1 = V + (j : ZMod (m + 1)) ∧ B.2 = U - (j : ZMod (m + 1))) ∨
        (B.1 = U - (j : ZMod (m + 1)) ∧ B.2 = V + (j : ZMod (m + 1)))) ∨ B = (R, R) := by
    intro B hBF p hp hpbt
    rcases hI2 p hpbt with hpR | ⟨j, hj, hjp⟩
    · by_cases hRR : (R, R) ∈ F
      · exact Or.inr (eq_of_shared_endpoint hdj hBF hRR hp (Or.inl hpR))
      · have hRV : R = V := hI4.resolve_left hRR
        obtain ⟨B', hB'F, hB'e⟩ := hI1 0 (by omega)
        have hpB' : p = B'.1 ∨ p = B'.2 := by
          have hpV : p = V := by rw [hRV] at hpR; exact hpR
          rcases hB'e with ⟨e1, e2⟩ | ⟨e1, e2⟩
          · rw [e1]
            exact Or.inl (by rw [hpV, Nat.cast_zero, add_zero])
          · rw [e2]
            exact Or.inr (by rw [hpV, Nat.cast_zero, add_zero])
        have hBB' := eq_of_shared_endpoint hdj hBF hB'F hp hpB'
        exact Or.inl ⟨0, by omega, by rw [hBB']; exact hB'e⟩
    · obtain ⟨B', hB'F, hB'e⟩ := hI1 j hj
      have hpB' : p = B'.1 ∨ p = B'.2 := by
        rcases hB'e with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · rcases hjp with hjp | hjp
          · exact Or.inl (by rw [e1]; exact hjp)
          · exact Or.inr (by rw [e2]; exact hjp)
        · rcases hjp with hjp | hjp
          · exact Or.inr (by rw [e2]; exact hjp)
          · exact Or.inl (by rw [e1]; exact hjp)
      have hBB' := eq_of_shared_endpoint hdj hBF hB'F hp hpB'
      exact Or.inl ⟨j, hj, by rw [hBB']; exact hB'e⟩
  -- case split: `A.1` in the arc or not
  by_cases hA1 : btw L A.1 Rt
  · rcases hchord A hAF A.1 (Or.inl rfl) hA1 with ⟨j, hj, hje⟩ | hAD
    · rcases hje with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2] <;> ring
    · rw [hAD]
      have hRR : (R, R) ∈ F := by rw [hAD] at hAF; exact hAF
      exact hRefl hRR
  · -- `A.1 = W`, and then also `A.2 = W`
    have hA1W : A.1 = W := (hclass A.1).resolve_left hA1
    have hWnarc : ¬ btw L W Rt := by rw [hA1W] at hA1; exact hA1
    have hsm : s + 2 * i = m + 1 := by
      by_contra hs2
      have hs3 : s + 2 * i = m + 2 := by omega
      have hRtLm : (Rt - L).val = m := by omega
      have hWL : W = L := by
        have e : W - L = 1 + (Rt - L) := by rw [hW]; ring
        have e2 : W - L = 0 := by
          have e3 : W - L = (((1 + (Rt - L).val : ℕ)) : ZMod (m + 1)) := by
            rw [e, Nat.cast_add, Nat.cast_one, ZMod.natCast_zmod_val]
          rw [e3]
          have e4 : 1 + (Rt - L).val = m + 1 := by omega
          rw [e4, ZMod.natCast_self]
        rw [sub_eq_zero] at e2
        exact e2
      rw [hWL] at hWnarc
      exact hWnarc ((btw_val LRt).2 (by simp))
    have hA2W : A.2 = W := by
      by_cases hA2 : btw L A.2 Rt
      · exfalso
        rcases hchord A hAF A.2 (Or.inr rfl) hA2 with ⟨j, hj, hje⟩ | hAD
        · rcases hje with ⟨e1, e2⟩ | ⟨e1, e2⟩
          · rw [e1] at hA1W
            have hbt := (hmem j hj).1
            rw [hA1W] at hbt
            exact hWnarc hbt
          · rw [e1] at hA1W
            have hbt := (hmem j hj).2
            rw [hA1W] at hbt
            exact hWnarc hbt
        · have hbt : btw L R Rt := hI5
          rw [hAD] at hA1W
          have hA1W' : R = W := hA1W
          rw [hA1W'] at hbt
          exact hWnarc hbt
      · exact (hclass A.2).resolve_left hA2
    have hAeq : A = (W, W) := Prod.ext hA1W hA2W
    have hWW : W + W = U + V := by
      have hW' : W = V + (i : ZMod (m + 1)) := by rw [hW, hRt]; ring
      have hz : (V - U) + ((2 * i : ℕ) : ZMod (m + 1)) = 0 := by
        have h2 : ((s + 2 * i : ℕ) : ZMod (m + 1)) = 0 := by
          rw [show s + 2 * i = m + 1 from by omega, ZMod.natCast_self]
        rw [← hcast] at h2
        exact h2
      have h3 : W + W = (U + V) + ((V - U) + ((2 * i : ℕ) : ZMod (m + 1))) := by
        rw [hW']; push_cast; ring
      rw [h3, hz, add_zero]
    rw [hAeq]
    exact hWW

/-- The peeling argument (two-degenerate version): starting from the central
configuration (the chord `{U, V}` whose interior is covered by `R`), every chord
of the family has sum `U + V`. -/
theorem peel_two {m : ℕ} {F : Finset (Chord (m + 1))}
    (hnc : ChordNonCrossing F) (hdj : ChordDisjoint F) (hal : ChordAligned F)
    (hcov : ∀ p : ZMod (m + 1), ∃ A ∈ F, p = A.1 ∨ p = A.2)
    (hdeg : ∀ A ∈ F, ∀ B ∈ F, A.1 = A.2 → B.1 = B.2 → A = B ∨ A.1 + A.1 = B.1 + B.1)
    {U V R : ZMod (m + 1)}
    (hUV1 : 1 ≤ (V - U).val) (_hUV2 : (V - U).val ≤ 2) (hRpos : (R - U).val ≤ (V - U).val)
    (hc0 : ∃ B ∈ F, (B.1 = V ∧ B.2 = U) ∨ (B.1 = U ∧ B.2 = V))
    (hint : ∀ p : ZMod (m + 1), sbtw U p V → p = R)
    (hR : (R, R) ∈ F ∨ R = V)
    (hRdj : (R, R) ∈ F → V ≠ R ∧ U ≠ R) :
    ∀ A ∈ F, A.1 + A.2 = U + V := by
  have hUV0 : U ≠ V := by
    intro he
    rw [he, sub_self, ZMod.val_zero] at hUV1
    omega
  have hbase : PeelInv F U V R 1 := by
    refine ⟨?_, ?_, ?_, hR, ?_, by have := ZMod.val_lt (V - U); omega⟩
    · intro j hj
      rw [Nat.lt_one_iff.1 hj]
      obtain ⟨B, hBF, hBe⟩ := hc0
      refine ⟨B, hBF, ?_⟩
      rw [Nat.cast_zero, add_zero, sub_zero]
      exact hBe
    · intro p hp
      rw [Nat.cast_one, sub_add_cancel, show V + 1 - 1 = V from by ring] at hp
      rcases btw_eq_or_sbtw hp hUV0 with h1 | h2 | h3
      · exact Or.inr ⟨0, by omega, Or.inr (by rw [h1, Nat.cast_zero, sub_zero])⟩
      · exact Or.inr ⟨0, by omega, Or.inl (by rw [h2, Nat.cast_zero, add_zero])⟩
      · exact Or.inl (hint p h3)
    · intro j hj hRR
      rw [Nat.lt_one_iff.1 hj, Nat.cast_zero, add_zero, sub_zero]
      exact hRdj hRR
    · rw [Nat.cast_one, sub_add_cancel, show V + 1 - 1 = V from by ring]
      exact (btw_val hUV0).2 hRpos
  have key : ∀ n : ℕ, ∀ i : ℕ, m + 2 - ((V - U).val + 2 * i) = n → 1 ≤ i →
      PeelInv F U V R i → ∀ A ∈ F, A.1 + A.2 = U + V := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n IH =>
      intro i hn hi hinv
      by_cases hf : m + 1 ≤ (V - U).val + 2 * i
      · exact peel_final_two hnc hdj hal hcov hdeg hi hUV1 hf hinv
      · have hroom : (V - U).val + 2 * i ≤ m := by omega
        have hinv' := peel_step_two hnc hdj hal hcov hdeg hi hUV1 hroom hinv
        exact IH (m + 2 - ((V - U).val + 2 * (i + 1))) (by omega) (i + 1) rfl (by omega) hinv'
  exact key (m + 2 - ((V - U).val + 2 * 1)) 1 rfl (le_refl 1) hbase

/-- The boundary-edge analysis (two-degenerate version): for a non-degenerate
chord `A0` minimizing the span `min ((A.2 - A.1).val) ((A.1 - A.2).val)` in a
non-crossing, vertex-disjoint, covering family, the span (in the minimizing
orientation `(P, Q)`) is either 1 (a boundary edge) or 2, in which case the
unique interior point is covered by a degenerate chord. The uniqueness hypothesis
on the degenerate chord is weakened to the antipodal condition: two consecutive
degenerate points `P + 1, P + 2` would force `2 = 0` in `ZMod (m + 1)`. -/
theorem boundary_analysis_two {m : ℕ} {F : Finset (Chord (m + 1))}
    (hnc : ChordNonCrossing F) (hdj : ChordDisjoint F)
    (hcov : ∀ p : ZMod (m + 1), ∃ A ∈ F, p = A.1 ∨ p = A.2)
    (hdeg : ∀ A ∈ F, ∀ B ∈ F, A.1 = A.2 → B.1 = B.2 → A = B ∨ A.1 + A.1 = B.1 + B.1)
    {A0 : Chord (m + 1)} (hA0F : A0 ∈ F) (_hA0ne : A0.1 ≠ A0.2)
    (hA0min : ∀ B ∈ F, B.1 ≠ B.2 → min (A0.2 - A0.1).val (A0.1 - A0.2).val ≤
      min (B.2 - B.1).val (B.1 - B.2).val)
    {P Q : ZMod (m + 1)} (hPQ : A0 = (P, Q) ∨ A0 = (Q, P))
    (hdPQ : (Q - P).val = min (A0.2 - A0.1).val (A0.1 - A0.2).val)
    (hd0 : 1 ≤ min (A0.2 - A0.1).val (A0.1 - A0.2).val) :
    (Q - P).val = 1 ∨ ((Q - P).val = 2 ∧ (P + 1, P + 1) ∈ F) := by
  -- a non-degenerate chord with an endpoint strictly inside the `(P, Q)` arc
  -- contradicts minimality
  have hmin : ∀ B ∈ F, B.1 ≠ B.2 → ∀ T : ZMod (m + 1), (T = B.1 ∨ T = B.2) →
      sbtw P T Q → False := by
    intro B hBF hBnd T hTp hTs
    have hTsne := sbtw_ne hTs
    have hBA0 : B ≠ A0 := by
      intro he
      rw [he] at hTp
      rcases hPQ with hPQe | hPQe
      · rw [hPQe] at hTp
        rcases hTp with h | h
        · exact hTsne.1 h.symm
        · exact hTsne.2.1 h
      · rw [hPQe] at hTp
        rcases hTp with h | h
        · exact hTsne.2.1 h
        · exact hTsne.1 h.symm
    obtain ⟨S, hBS⟩ : ∃ S, (B.1 = T ∧ B.2 = S) ∨ (B.1 = S ∧ B.2 = T) := by
      rcases hTp with h | h
      · exact ⟨B.2, Or.inl ⟨h.symm, rfl⟩⟩
      · exact ⟨B.1, Or.inr ⟨rfl, h.symm⟩⟩
    have hTS : T ≠ S := by
      rcases hBS with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · intro he; exact hBnd (by rw [e1, e2, he])
      · intro he; exact hBnd (by rw [e1, e2, ← he])
    have hSs : sbtw P S Q := by
      have hnc' := hnc A0 hA0F B hBF hBA0.symm
      rcases hPQ with hPQe | hPQe
      · rw [hPQe] at hnc'
        rcases hBS with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · rw [e1, e2] at hnc'
          exact hnc'.1 hTs
        · rw [e1, e2] at hnc'
          exact hnc'.2 hTs
      · rw [hPQe] at hnc'
        have hTrev : ¬ sbtw Q T P := (sbtw_not_reverse hTsne.1 hTsne.2.1 hTsne.2.2.symm).1 hTs
        have hSS : S ≠ P ∧ S ≠ Q := by
          have hd := hdj A0 hA0F B hBF hBA0.symm
          rw [hPQe] at hd
          rcases hBS with ⟨e1, e2⟩ | ⟨e1, e2⟩
          · rw [e1, e2] at hd
            exact ⟨hd.2.2.2.symm, hd.2.1.symm⟩
          · rw [e1, e2] at hd
            exact ⟨hd.2.2.1.symm, hd.1.symm⟩
        rcases hBS with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · rw [e1, e2] at hnc'
          have h1 : ¬ sbtw Q S P := fun hs => hTrev (hnc'.2 hs)
          rcases sbtw_or_sbtw_rev hSS.1 hSS.2 hTsne.2.2 with hs | hs
          · exact hs
          · exact absurd hs h1
        · rw [e1, e2] at hnc'
          have h1 : ¬ sbtw Q S P := fun hs => hTrev (hnc'.1 hs)
          rcases sbtw_or_sbtw_rev hSS.1 hSS.2 hTsne.2.2 with hs | hs
          · exact hs
          · exact absurd hs h1
    -- value bounds for the two endpoints
    have hTsne2 := sbtw_ne hSs
    have hTP : 1 ≤ (T - P).val ∧ (T - P).val < (Q - P).val := by
      rw [sbtw_val hTsne.1] at hTs
      refine ⟨?_, hTs⟩
      rcases Nat.eq_zero_or_pos (T - P).val with hz | hz
      · exfalso
        apply hTsne.1
        have e := ZMod.natCast_zmod_val (T - P)
        rw [hz, Nat.cast_zero] at e
        have e' : T - P = 0 := e.symm
        rw [sub_eq_zero] at e'
        exact e'.symm
      · exact hz
    have hSP : 1 ≤ (S - P).val ∧ (S - P).val < (Q - P).val := by
      rw [sbtw_val hTsne2.1] at hSs
      refine ⟨?_, hSs⟩
      rcases Nat.eq_zero_or_pos (S - P).val with hz | hz
      · exfalso
        apply hTsne2.1
        have e := ZMod.natCast_zmod_val (S - P)
        rw [hz, Nat.cast_zero] at e
        have e' : S - P = 0 := e.symm
        rw [sub_eq_zero] at e'
        exact e'.symm
      · exact hz
    -- one of the two orientations has a smaller span
    have hdB : min (B.2 - B.1).val (B.1 - B.2).val < (Q - P).val := by
      have hdif : (S - T).val = (S - P).val - (T - P).val ∨
          (T - S).val = (T - P).val - (S - P).val := by
        by_cases hle : (S - P).val ≤ (T - P).val
        · right
          have e : T - S = ((((T - P).val - (S - P).val : ℕ)) : ZMod (m + 1)) := by
            have e1 := ZMod.natCast_zmod_val (T - P)
            have e2 := ZMod.natCast_zmod_val (S - P)
            have e3 : T - S = (T - P) - (S - P) := by ring
            rw [e3, Nat.cast_sub hle, e1, e2]
          rw [e, val_natCast_of_lt (by have := ZMod.val_lt (T - P); omega)]
        · left
          have e : S - T = ((((S - P).val - (T - P).val : ℕ)) : ZMod (m + 1)) := by
            have e1 := ZMod.natCast_zmod_val (S - P)
            have e2 := ZMod.natCast_zmod_val (T - P)
            have e3 : S - T = (S - P) - (T - P) := by ring
            rw [e3, Nat.cast_sub (by omega : (T - P).val ≤ (S - P).val), e1, e2]
          rw [e, val_natCast_of_lt (by have := ZMod.val_lt (S - P); omega)]
      rcases hdif with h | h
      · have hlt : (S - T).val < (Q - P).val := by omega
        rcases hBS with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · rw [e1, e2]
          exact lt_of_le_of_lt (min_le_left _ _) hlt
        · rw [e1, e2]
          exact lt_of_le_of_lt (min_le_right _ _) hlt
      · have hlt : (T - S).val < (Q - P).val := by omega
        rcases hBS with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · rw [e1, e2]
          exact lt_of_le_of_lt (min_le_right _ _) hlt
        · rw [e1, e2]
          exact lt_of_le_of_lt (min_le_left _ _) hlt
    have hBle := hA0min B hBF hBnd
    omega
  -- the span is at most 2
  have hd2 : (Q - P).val ≤ 2 := by
    by_contra h3
    push Not at h3
    have hm2 : 2 ≤ m := by have := ZMod.val_lt (Q - P); omega
    have hne1 : P ≠ P + 1 := by
      intro he
      have e : (1 : ZMod (m + 1)) = 0 := by linear_combination -he
      have e2 : (1 : ZMod (m + 1)).val = 1 := val_one' (by omega : 1 ≤ m)
      rw [e, ZMod.val_zero] at e2
      omega
    have hne2 : P ≠ P + 2 := by
      intro he
      have e : (2 : ZMod (m + 1)) = 0 := by linear_combination -he
      have e2 : (2 : ZMod (m + 1)).val = 2 := by
        have e2' : (2 : ZMod (m + 1)) = ((2 : ℕ) : ZMod (m + 1)) := by push_cast; ring
        rw [e2', val_natCast_of_lt (by omega : 2 < m + 1)]
      rw [e, ZMod.val_zero] at e2
      omega
    have hR1 : sbtw P (P + 1) Q := by
      rw [sbtw_val hne1]
      have e : P + 1 - P = 1 := by ring
      rw [e, val_one' (by omega : 1 ≤ m)]
      omega
    have hR2 : sbtw P (P + 2) Q := by
      rw [sbtw_val hne2]
      have e : P + 2 - P = ((2 : ℕ) : ZMod (m + 1)) := by
        rw [show ((2 : ℕ) : ZMod (m + 1)) = 2 from by push_cast; ring]; ring
      rw [e, val_natCast_of_lt (by omega : 2 < m + 1)]
      omega
    obtain ⟨B1, hB1F, hB1e⟩ := hcov (P + 1)
    obtain ⟨B2, hB2F, hB2e⟩ := hcov (P + 2)
    by_cases hB1nd : B1.1 ≠ B1.2
    · exact hmin B1 hB1F hB1nd (P + 1) (by
        rcases hB1e with h | h
        · exact Or.inl h
        · exact Or.inr h) hR1
    · by_cases hB2nd : B2.1 ≠ B2.2
      · exact hmin B2 hB2F hB2nd (P + 2) (by
          rcases hB2e with h | h
          · exact Or.inl h
          · exact Or.inr h) hR2
      · push Not at hB1nd hB2nd
        have e := hdeg B1 hB1F B2 hB2F hB1nd hB2nd
        have g1 : P + 1 = B1.1 := by
          rcases hB1e with h | h
          · exact h
          · rw [← hB1nd] at h; exact h
        have g2 : P + 2 = B2.1 := by
          rcases hB2e with h | h
          · exact h
          · rw [← hB2nd] at h; exact h
        rcases e with e | e
        · -- equal chords: `P + 1 = P + 2`, impossible
          have g3 : P + 1 = P + 2 := by rw [g1, g2, e]
          have e2 : (1 : ZMod (m + 1)) = 2 := by linear_combination g3
          have e3 : (1 : ZMod (m + 1)).val = 1 := val_one' (by omega : 1 ≤ m)
          have e4 : (2 : ZMod (m + 1)).val = 2 := by
            have e4' : (2 : ZMod (m + 1)) = ((2 : ℕ) : ZMod (m + 1)) := by push_cast; ring
            rw [e4', val_natCast_of_lt (by omega : 2 < m + 1)]
          rw [e2, e4] at e3
          omega
        · -- antipodal chords: `2(P + 1) = 2(P + 2)`, i.e. `2 = 0` in `ZMod (m + 1)`,
          -- impossible since `m ≥ 2`
          rw [← g1, ← g2] at e
          have e2 : (2 : ZMod (m + 1)) = 0 := by linear_combination -e
          have e4 : (2 : ZMod (m + 1)).val = 2 := by
            have e4' : (2 : ZMod (m + 1)) = ((2 : ℕ) : ZMod (m + 1)) := by push_cast; ring
            rw [e4', val_natCast_of_lt (by omega : 2 < m + 1)]
          rw [e2, ZMod.val_zero] at e4
          omega
  rcases eq_or_ne (Q - P).val 1 with hd1 | hd1
  · exact Or.inl hd1
  · right
    have hd2' : (Q - P).val = 2 := by omega
    refine ⟨hd2', ?_⟩
    have hm2 : 2 ≤ m := by have := ZMod.val_lt (Q - P); omega
    have hne1 : P ≠ P + 1 := by
      intro he
      have e : (1 : ZMod (m + 1)) = 0 := by linear_combination -he
      have e2 : (1 : ZMod (m + 1)).val = 1 := val_one' (by omega : 1 ≤ m)
      rw [e, ZMod.val_zero] at e2
      omega
    have hR1 : sbtw P (P + 1) Q := by
      rw [sbtw_val hne1]
      have e : P + 1 - P = 1 := by ring
      rw [e, val_one' (by omega : 1 ≤ m), hd2']
      omega
    obtain ⟨B1, hB1F, hB1e⟩ := hcov (P + 1)
    by_cases hB1nd : B1.1 ≠ B1.2
    · exact (hmin B1 hB1F hB1nd (P + 1) (by
        rcases hB1e with h | h
        · exact Or.inl h
        · exact Or.inr h) hR1).elim
    · push Not at hB1nd
      have g1 : B1.1 = P + 1 := by
        rcases hB1e with h | h
        · exact h.symm
        · rw [← hB1nd] at h; exact h.symm
      have g2 : B1 = (P + 1, P + 1) := Prod.ext g1 (hB1nd.symm.trans g1)
      rw [g2] at hB1F
      exact hB1F

/-- The minimal-span non-degenerate chord gives either a boundary edge or a
span-2 chord around a degenerate point (two-degenerate version: uniqueness of the
degenerate chord is replaced by the antipodal condition, and the existence of a
non-degenerate chord is assumed instead). -/
theorem boundary_data_two {m : ℕ} {F : Finset (Chord (m + 1))}
    (hnc : ChordNonCrossing F) (hdj : ChordDisjoint F)
    (hcov : ∀ p : ZMod (m + 1), ∃ A ∈ F, p = A.1 ∨ p = A.2)
    (hdeg : ∀ A ∈ F, ∀ B ∈ F, A.1 = A.2 → B.1 = B.2 → A = B ∨ A.1 + A.1 = B.1 + B.1)
    (hnd : ∃ A ∈ F, A.1 ≠ A.2) :
    (∃ U V : ZMod (m + 1), (V - U).val = 1 ∧
      ∃ B ∈ F, (B.1 = V ∧ B.2 = U) ∨ (B.1 = U ∧ B.2 = V)) ∨
    (∃ U V R : ZMod (m + 1), (V - U).val = 2 ∧ (R - U).val = 1 ∧ (R, R) ∈ F ∧
      ∃ B ∈ F, (B.1 = V ∧ B.2 = U) ∨ (B.1 = U ∧ B.2 = V)) := by
  obtain ⟨A', hA'F, hA'ne⟩ := hnd
  have hS : (F.filter fun A => A.1 ≠ A.2).Nonempty :=
    ⟨A', Finset.mem_filter.2 ⟨hA'F, hA'ne⟩⟩
  obtain ⟨A0, hA0, hA0min⟩ := Finset.exists_min_image _
    (fun A => min (A.2 - A.1).val (A.1 - A.2).val) hS
  rw [Finset.mem_filter] at hA0
  obtain ⟨hA0F, hA0ne⟩ := hA0
  have hA0min' : ∀ B ∈ F, B.1 ≠ B.2 → min (A0.2 - A0.1).val (A0.1 - A0.2).val ≤
      min (B.2 - B.1).val (B.1 - B.2).val := by
    intro B hBF hBne
    exact hA0min B (Finset.mem_filter.2 ⟨hBF, hBne⟩)
  have hd0 : 1 ≤ min (A0.2 - A0.1).val (A0.1 - A0.2).val := by
    have h1 : (A0.2 - A0.1).val ≠ 0 := fun hz => hA0ne (by
      have e := ZMod.natCast_zmod_val (A0.2 - A0.1)
      rw [hz, Nat.cast_zero] at e
      have e' : A0.2 - A0.1 = 0 := e.symm
      rw [sub_eq_zero] at e'
      exact e'.symm)
    have h2 : (A0.1 - A0.2).val ≠ 0 := fun hz => hA0ne (by
      have e := ZMod.natCast_zmod_val (A0.1 - A0.2)
      rw [hz, Nat.cast_zero] at e
      have e' : A0.1 - A0.2 = 0 := e.symm
      rw [sub_eq_zero] at e'
      exact e')
    omega
  by_cases hle : (A0.2 - A0.1).val ≤ (A0.1 - A0.2).val
  · -- orient `P = A0.1`, `Q = A0.2`
    have hdPQ : (A0.2 - A0.1).val = min (A0.2 - A0.1).val (A0.1 - A0.2).val :=
      (min_eq_left hle).symm
    have hPQ : A0 = (A0.1, A0.2) ∨ A0 = (A0.2, A0.1) := Or.inl (Prod.eta A0).symm
    rcases boundary_analysis_two hnc hdj hcov hdeg hA0F hA0ne hA0min' hPQ hdPQ hd0 with hd1 | ⟨hd2, hR⟩
    · exact Or.inl ⟨A0.1, A0.2, hd1, A0, hA0F, Or.inr ⟨rfl, rfl⟩⟩
    · exact Or.inr ⟨A0.1, A0.2, A0.1 + 1, hd2, by
        have e : A0.1 + 1 - A0.1 = 1 := by ring
        rw [e, val_one' (by have := ZMod.val_lt (A0.2 - A0.1); omega)], hR, A0, hA0F, Or.inr ⟨rfl, rfl⟩⟩
  · -- orient `P = A0.2`, `Q = A0.1`
    have hdPQ : (A0.1 - A0.2).val = min (A0.2 - A0.1).val (A0.1 - A0.2).val :=
      (min_eq_right (by omega : (A0.1 - A0.2).val ≤ (A0.2 - A0.1).val)).symm
    have hPQ : A0 = (A0.2, A0.1) ∨ A0 = (A0.1, A0.2) := Or.inr (Prod.eta A0).symm
    rcases boundary_analysis_two hnc hdj hcov hdeg hA0F hA0ne hA0min' hPQ hdPQ hd0 with hd1 | ⟨hd2, hR⟩
    · exact Or.inl ⟨A0.2, A0.1, hd1, A0, hA0F, Or.inl ⟨rfl, rfl⟩⟩
    · exact Or.inr ⟨A0.2, A0.1, A0.2 + 1, hd2, by
        have e : A0.2 + 1 - A0.2 = 1 := by ring
        rw [e, val_one' (by have := ZMod.val_lt (A0.1 - A0.2); omega)], hR, A0, hA0F, Or.inl ⟨rfl, rfl⟩⟩

/-- The two-degenerate strengthening of `const_sum_of_aligned`: the family may
have up to two degenerate chords, but then their endpoint sums agree (the two
degenerate chords sit at antipodal points). The whole family still has constant
endpoint-sum. -/
theorem const_sum_of_aligned_two {m : ℕ} (F : Finset (Chord (m + 1)))
    (hnc : ChordNonCrossing F) (hdj : ChordDisjoint F) (hal : ChordAligned F)
    (hcov : ∀ p : ZMod (m + 1), ∃ A ∈ F, p = A.1 ∨ p = A.2)
    (hdeg : ∀ A ∈ F, ∀ B ∈ F, A.1 = A.2 → B.1 = B.2 → A = B ∨ A.1 + A.1 = B.1 + B.1) :
    ∃ c₀ : ZMod (m + 1), ∀ A ∈ F, A.1 + A.2 = c₀ := by
  rcases F.eq_empty_or_nonempty with hF | hF
  · -- `F` empty is impossible: the circle is nonempty but must be covered
    exfalso
    obtain ⟨A, hA, -⟩ := hcov 0
    rw [hF] at hA
    simp at hA
  · by_cases hF1 : F.card = 1
    · -- a single chord: take `c₀` to be its sum
      obtain ⟨A, hA⟩ := Finset.card_eq_one.1 hF1
      refine ⟨A.1 + A.2, ?_⟩
      intro B hB
      rw [hA] at hB
      rw [Finset.mem_singleton.1 hB]
    · by_cases hall : ∀ A ∈ F, A.1 = A.2
      · -- all chords degenerate: every point carries a degenerate chord, so any two
        -- distinct points are antipodal; this forces `m + 1 ≤ 2`, and then `2 = 0`
        refine ⟨0, fun A hAF => ?_⟩
        have hm1 : m ≤ 1 := by
          by_contra hm1
          push Not at hm1
          obtain ⟨A0, hA0F, hA0e⟩ := hcov 0
          obtain ⟨A1, hA1F, hA1e⟩ := hcov 1
          have hA0eq : A0 = (0, 0) := by
            rcases hA0e with h | h
            · exact Prod.ext h.symm ((hall A0 hA0F).symm.trans h.symm)
            · exact Prod.ext ((hall A0 hA0F).trans h.symm) h.symm
          have hA1eq : A1 = (1, 1) := by
            rcases hA1e with h | h
            · exact Prod.ext h.symm ((hall A1 hA1F).symm.trans h.symm)
            · exact Prod.ext ((hall A1 hA1F).trans h.symm) h.symm
          have h01 : (0 : ZMod (m + 1)) ≠ 1 := by
            intro he
            have e1 : (1 : ZMod (m + 1)).val = 1 := val_one' (by omega : 1 ≤ m)
            rw [← he, ZMod.val_zero] at e1
            omega
          rcases hdeg A0 hA0F A1 hA1F (hall A0 hA0F) (hall A1 hA1F) with e | e
          · rw [hA0eq, hA1eq] at e
            exact h01 (Prod.ext_iff.1 e).1
          · rw [hA0eq, hA1eq] at e
            have e2 : (2 : ZMod (m + 1)) = 0 := by
              have ee : (0 : ZMod (m + 1)) + 0 = 1 + 1 := e
              linear_combination -ee
            have e3 : (2 : ZMod (m + 1)).val = 2 := by
              have e3' : (2 : ZMod (m + 1)) = ((2 : ℕ) : ZMod (m + 1)) := by push_cast; ring
              rw [e3', val_natCast_of_lt (by omega : 2 < m + 1)]
            rw [e2, ZMod.val_zero] at e3
            omega
        have h2 : (2 : ZMod (m + 1)) = 0 := by
          interval_cases m <;> decide
        rw [(hall A hAF).symm, ← two_mul, h2, zero_mul]
      · -- a non-degenerate chord exists: the boundary analysis, then peeling
        push Not at hall
        obtain ⟨A', hA'F, hA'ne⟩ := hall
        rcases boundary_data_two hnc hdj hcov hdeg ⟨A', hA'F, hA'ne⟩ with
          ⟨U, V, hUV, hc0⟩ | ⟨U, V, R, hUV, hRU, hRR, hc0⟩
        · -- boundary edge `{U, V}` with `V = U + 1`: peel with dummy `R = V`
          refine ⟨U + V, peel_two hnc hdj hal hcov hdeg (by omega : 1 ≤ (V - U).val)
            (by omega : (V - U).val ≤ 2) (by omega : (V - U).val ≤ (V - U).val) hc0 ?_ (Or.inr rfl) ?_⟩
          · intro p hp
            exfalso
            have hpU : p = U := by
              by_contra hUp
              rw [sbtw_val (Ne.symm hUp), hUV] at hp
              have h1 : (p - U).val = 0 := by omega
              apply hUp
              have e : p - U = 0 := by
                have e2 := ZMod.natCast_zmod_val (p - U)
                rw [h1, Nat.cast_zero] at e2
                exact e2.symm
              rw [sub_eq_zero] at e
              exact e
            rw [hpU, sbtw_zmod_def] at hp
            omega
          · intro hVV
            exfalso
            obtain ⟨B, hBF, hBe⟩ := hc0
            have hne : (V, V) ≠ B := by
              intro he
              rcases hBe with ⟨e1, e2⟩ | ⟨e1, e2⟩
              · have h2 : (V, V).2 = B.2 := by rw [he]
                rw [e2] at h2
                have h2' : V = U := h2
                rw [show V - U = 0 from by rw [h2', sub_self], ZMod.val_zero] at hUV
                omega
              · have h2 : (V, V).1 = B.1 := by rw [he]
                rw [e1] at h2
                have h2' : V = U := h2
                rw [show V - U = 0 from by rw [h2', sub_self], ZMod.val_zero] at hUV
                omega
            have hd := hdj (V, V) hVV B hBF hne
            rcases hBe with ⟨e1, e2⟩ | ⟨e1, e2⟩
            · rw [e1] at hd
              exact hd.1 rfl
            · rw [e2] at hd
              exact hd.2.1 rfl
        · -- span-2 chord `{U, V}` around the degenerate point `R = U + 1`
          have hVR : V ≠ R := by
            intro he
            rw [he, hRU] at hUV
            omega
          have hUR : U ≠ R := by
            intro he
            rw [← he, sub_self, ZMod.val_zero] at hRU
            omega
          refine ⟨U + V, peel_two hnc hdj hal hcov hdeg (by omega : 1 ≤ (V - U).val)
            (by omega : (V - U).val ≤ 2) (by omega : (R - U).val ≤ (V - U).val) hc0 ?_ (Or.inl hRR)
            (fun _ => ⟨hVR, hUR⟩)⟩
          · intro p hp
            have hUp : U ≠ p := by
              intro he
              rw [← he, sbtw_zmod_def] at hp
              omega
            rw [sbtw_val hUp, hUV] at hp
            have hp1 : (p - U).val = 1 := by
              have h0 : (p - U).val ≠ 0 := by
                intro hz
                apply hUp
                have e : p - U = 0 := by
                  have e2 := ZMod.natCast_zmod_val (p - U)
                  rw [hz, Nat.cast_zero] at e2
                  exact e2.symm
                rw [sub_eq_zero] at e
                exact e.symm
              omega
            have e : p - U = 1 := ZMod.val_injective _ (by
              rw [hp1, val_one' (by have := ZMod.val_lt (V - U); omega)])
            have eR : R - U = 1 := ZMod.val_injective _ (by
              rw [hRU, val_one' (by have := ZMod.val_lt (V - U); omega)])
            exact sub_left_injective (show p - U = R - U from by rw [e, eR])

/-- The parallel extension condition: every `(n+1)`-chord of the inserted
arrangement has endpoint position-sum equal to the position of the new label.
This is the algebraic form of the official solution's "the n-chords of S are
parallel". -/
def ExtParallel {n : ℕ} (τ : ZMod (n + 1) ≃ ZMod (n + 1)) (c : ZMod (n + 1)) : Prop :=
  ∀ A ∈ kChords (InsertNorm τ c) (n + 1), A.1 + A.2 = (InsertNorm τ c) topLabel

/-- The `(n+1)`-chord through labels `0` and `n + 1` of an inserted arrangement. -/
theorem mem_kChords_zero_top {n : ℕ} (τ : ZMod (n + 1) ≃ ZMod (n + 1)) (c : ZMod (n + 1)) :
    (InsertNorm τ c 0, InsertNorm τ c topLabel) ∈ kChords (InsertNorm τ c) (n + 1) := by
  rw [mem_kChords]
  refine ⟨0, topLabel, ?_, ?_, rfl⟩
  · rw [ZMod.val_zero, topLabel_val, Nat.zero_add]
  · rw [ZMod.val_zero]
    exact Nat.zero_le _

/-- Beauty of the extension implies the parallel condition: the `(n+1)`-chords are
aligned and cover every point with at most one degenerate chord, so the structure
theorem makes their endpoint sums constant, and the chord through `0` and `n + 1`
pins the constant to the position of the new label. -/
theorem Beautiful.extParallel {n : ℕ} {τ : ZMod (n + 1) ≃ ZMod (n + 1)} {c : ZMod (n + 1)}
    (h : Beautiful (InsertNorm τ c)) : ExtParallel τ c := by
  have hnc := Beautiful.kChords_nonCrossing h (n + 1)
  have hdj := kChords_disjoint (σ := InsertNorm τ c) (k := n + 1)
  have hal := aligned_kChords (n + 2) (InsertNorm τ c) h (n + 1)
  have hmem := mem_kChords_zero_top τ c
  have hcov : ∀ p : ZMod (n + 2), ∃ A ∈ kChords (InsertNorm τ c) (n + 1),
      p = A.1 ∨ p = A.2 := by
    intro p
    obtain ⟨x, rfl⟩ := Equiv.surjective (InsertNorm τ c) p
    by_cases hx0 : x = 0
    · subst hx0
      exact ⟨(_, _), hmem, Or.inl rfl⟩
    · by_cases hxt : x = topLabel
      · subst hxt
        exact ⟨(_, _), hmem, Or.inr rfl⟩
      · have hxv0 : x.val ≠ 0 := by
          intro he
          apply hx0
          rw [← ZMod.natCast_zmod_val x, he, Nat.cast_zero]
        have hxvt : x.val ≠ n + 1 := by
          intro he
          apply hxt
          apply ZMod.val_injective _
          rw [he, topLabel_val]
        set y := (((n + 1) - x.val : ℕ) : ZMod (n + 2)) with hydef
        have hxlt := ZMod.val_lt x
        have hyv : y.val = (n + 1) - x.val := by
          rw [hydef, ZMod.val_natCast, Nat.mod_eq_of_lt (by have := ZMod.val_lt x; omega :
            (n + 1) - x.val < n + 2)]
        rcases le_or_gt x.val y.val with hle | hle
        · refine ⟨(InsertNorm τ c x, InsertNorm τ c y), ?_, Or.inl rfl⟩
          rw [mem_kChords]
          exact ⟨x, y, by omega, hle, rfl⟩
        · refine ⟨(InsertNorm τ c y, InsertNorm τ c x), ?_, Or.inr rfl⟩
          rw [mem_kChords]
          exact ⟨y, x, by omega, by omega, rfl⟩
  have hdeg : ∀ A ∈ kChords (InsertNorm τ c) (n + 1), ∀ B ∈ kChords (InsertNorm τ c) (n + 1),
      A.1 = A.2 → B.1 = B.2 → A = B := by
    intro A hA B hB hAdeg hBdeg
    obtain ⟨xa, ya, hsa, hlea, hAe⟩ := mem_kChords.mp hA
    obtain ⟨xb, yb, hsb, hleb, hBe⟩ := mem_kChords.mp hB
    have hxa : xa = ya := by
      apply (InsertNorm τ c).injective
      rw [hAe] at hAdeg
      exact hAdeg
    have hxb : xb = yb := by
      apply (InsertNorm τ c).injective
      rw [hBe] at hBdeg
      exact hBdeg
    rw [← hxa] at hsa
    rw [← hxb] at hsb
    have h2 : xa.val = xb.val := by omega
    have h3 : xa = xb := ZMod.val_injective _ h2
    have h4 : ya = yb := by
      rw [← hxa, ← hxb]
      exact h3
    rw [hAe, hBe, h3, h4]
  obtain ⟨c₀, hc₀⟩ := const_sum_of_aligned (kChords (InsertNorm τ c) (n + 1)) hnc hdj hal hcov hdeg
  have hpin := hc₀ _ hmem
  simp only [InsertNorm_zero, zero_add] at hpin
  intro A hA
  rw [hpin]
  exact hc₀ A hA

/-- Reflection `x ↦ q - x` reverses the circle orientation. -/
theorem sbtw_reflect {N : ℕ} [NeZero N] {q a b c : ZMod N} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) :
    sbtw a b c ↔ sbtw (q - a) (q - c) (q - b) := by
  rw [sbtw_val hab, sbtw_val (fun h => hac (by linear_combination -h : a = c))]
  have e1 : (q - c) - (q - a) = a - c := by ring
  have e2 : (q - b) - (q - a) = a - b := by ring
  rw [e1, e2]
  have v1 : (b - a).val = N - (a - b).val := by
    have e : b - a = -(a - b) := by ring
    rw [e, val_neg'' (sub_ne_zero.mpr hab)]
  have v2 : (c - a).val = N - (a - c).val := by
    have e : c - a = -(a - c) := by ring
    rw [e, val_neg'' (sub_ne_zero.mpr hac)]
  have hu : (a - b).val ≠ 0 := by
    intro he
    apply hab
    have h6 : a - b = 0 := by
      rw [← ZMod.natCast_zmod_val (a - b), he, Nat.cast_zero]
    exact sub_eq_zero.mp h6
  have hv : (a - c).val ≠ 0 := by
    intro he
    apply hac
    have h6 : a - c = 0 := by
      rw [← ZMod.natCast_zmod_val (a - c), he, Nat.cast_zero]
    exact sub_eq_zero.mp h6
  have h1 := ZMod.val_lt (a - b)
  have h2 := ZMod.val_lt (a - c)
  rw [v1, v2]
  omega

/-- Under the parallel condition, reflection `x ↦ q - x` sends the position of a
label to the position of its partner label `n + 1 - x`. -/
theorem ExtParallel.refl_apply {n : ℕ} {τ : ZMod (n + 1) ≃ ZMod (n + 1)} {c : ZMod (n + 1)}
    (h : ExtParallel τ c) (x : ZMod (n + 2)) :
    (InsertNorm τ c) (topLabel - x) = (InsertNorm τ c) topLabel - (InsertNorm τ c) x := by
  have hval : (topLabel - x).val = (n + 1) - x.val := by
    have e : (topLabel : ZMod (n + 2)) - x = (((n + 1) - x.val : ℕ) : ZMod (n + 2)) := by
      show (((n + 1 : ℕ) : ZMod (n + 2)) - x) = _
      conv_lhs => rw [← ZMod.natCast_zmod_val x]
      rw [← Nat.cast_sub (by have := ZMod.val_lt x; omega : x.val ≤ n + 1)]
    rw [e, ZMod.val_natCast, Nat.mod_eq_of_lt (by have := ZMod.val_lt x; omega :
      (n + 1) - x.val < n + 2)]
  have hxlt := ZMod.val_lt x
  have hmem : (InsertNorm τ c x, InsertNorm τ c (topLabel - x)) ∈
      kChords (InsertNorm τ c) (n + 1) ∨
      (InsertNorm τ c (topLabel - x), InsertNorm τ c x) ∈
      kChords (InsertNorm τ c) (n + 1) := by
    rcases le_or_gt x.val (topLabel - x).val with hle | hle
    · exact Or.inl (by rw [mem_kChords]; exact ⟨x, topLabel - x, by omega, hle, rfl⟩)
    · exact Or.inr (by rw [mem_kChords]; exact ⟨topLabel - x, x, by omega, by omega, rfl⟩)
  rcases hmem with hm | hm
  · have h1 := h _ hm
    linear_combination h1
  · have h1 := h _ hm
    linear_combination h1

/-- The parallel condition makes the `(n+1)`-chords non-crossing (constant
endpoint-sum chords do not cross). -/
theorem ExtParallel.nonCross_eq {n : ℕ} {τ : ZMod (n + 1) ≃ ZMod (n + 1)} {c : ZMod (n + 1)}
    (h : ExtParallel τ c) : ChordNonCrossing (kChords (InsertNorm τ c) (n + 1)) := by
  intro A hA B hB hne
  obtain ⟨d1, d2, d3, d4⟩ := kChords_disjoint A hA B hB hne
  have e1 : (InsertNorm τ c) topLabel - A.1 = A.2 := by
    have h1 := h A hA
    linear_combination -h1
  have e2 : (InsertNorm τ c) topLabel - B.1 = B.2 := by
    have h1 := h B hB
    linear_combination -h1
  rw [← e1, ← e2]
  exact sbtw_sum_const d1 (by rw [e2]; exact d2.symm)

/-- Chords of sum `< n + 1` of the inserted arrangement come from the rotated
original arrangement, hence are non-crossing. -/
theorem ExtParallel.nonCross_lt {n : ℕ} {τ : ZMod (n + 1) ≃ ZMod (n + 1)} (hτ : Beautiful τ)
    {c : ZMod (n + 1)} {k : ℕ} (hk : k < n + 1) :
    ChordNonCrossing (kChords (InsertNorm τ c) k) := by
  intro A hA B hB hne
  obtain ⟨xa, ya, hsa, hlea, hAe⟩ := mem_kChords.mp hA
  obtain ⟨xb, yb, hsb, hleb, hBe⟩ := mem_kChords.mp hB
  set ρ := rot c τ with hρdef
  set q : ZMod (n + 2) := (((n + 1) - (ρ 0).val : ℕ) : ZMod (n + 2)) with hqdef
  have hS : InsertNorm τ c = Insert ρ q := rfl
  have hτ' : Beautiful ρ := hτ.rot c
  have hncρ := Beautiful.kChords_nonCrossing hτ' k
  have hn : ∀ x y : ZMod (n + 2), x.val + y.val = k → x ≠ topLabel := by
    intro x y hxs he
    rw [he, topLabel_val] at hxs
    omega
  have hxan : xa ≠ topLabel := hn xa ya hsa
  have hxbn : xb ≠ topLabel := hn xb yb hsb
  have hya2 : ya.val ≤ n := by omega
  have hyb2 : yb.val ≤ n := by omega
  have hyan : ya ≠ topLabel := by
    intro he
    rw [he, topLabel_val] at hya2
    omega
  have hybn : yb ≠ topLabel := by
    intro he
    rw [he, topLabel_val] at hyb2
    omega
  have hSapp : ∀ x : ZMod (n + 2), x ≠ topLabel →
      InsertNorm τ c x = circleIncl q (ρ ((x.val : ℕ) : ZMod (n + 1))) := by
    intro x hx
    rw [hS, Insert_apply_ne_top ρ q hx]
    show circleIncl q (ρ ((labelInclEquiv).symm ⟨x, hx⟩)) =
      circleIncl q (ρ ((x.val : ℕ) : ZMod (n + 1)))
    rw [show (labelInclEquiv).symm ⟨x, hx⟩ = ((x.val : ℕ) : ZMod (n + 1)) from rfl]
  have hv : ∀ x : ZMod (n + 2), x.val ≤ k → (((x.val : ℕ) : ZMod (n + 1))).val = x.val := by
    intro x hx
    exact ZMod.val_cast_of_lt (by omega : x.val < n + 1)
  have hA' : (ρ ((xa.val : ℕ) : ZMod (n + 1)), ρ ((ya.val : ℕ) : ZMod (n + 1))) ∈
      kChords ρ k := by
    rw [mem_kChords]
    exact ⟨_, _, by rw [hv xa (by omega), hv ya (by omega)]; exact hsa,
      by rw [hv xa (by omega), hv ya (by omega)]; exact hlea, rfl⟩
  have hB' : (ρ ((xb.val : ℕ) : ZMod (n + 1)), ρ ((yb.val : ℕ) : ZMod (n + 1))) ∈
      kChords ρ k := by
    rw [mem_kChords]
    exact ⟨_, _, by rw [hv xb (by omega), hv yb (by omega)]; exact hsb,
      by rw [hv xb (by omega), hv yb (by omega)]; exact hleb, rfl⟩
  have hne' : (ρ ((xa.val : ℕ) : ZMod (n + 1)), ρ ((ya.val : ℕ) : ZMod (n + 1))) ≠
      (ρ ((xb.val : ℕ) : ZMod (n + 1)), ρ ((yb.val : ℕ) : ZMod (n + 1))) := by
    intro he
    apply hne
    rw [hAe, hBe]
    obtain ⟨h1, h2⟩ := Prod.ext_iff.mp he
    have e1 : ρ ((xa.val : ℕ) : ZMod (n + 1)) = ρ ((xb.val : ℕ) : ZMod (n + 1)) := h1
    have e2 : ρ ((ya.val : ℕ) : ZMod (n + 1)) = ρ ((yb.val : ℕ) : ZMod (n + 1)) := h2
    have f1 : ((xa.val : ℕ) : ZMod (n + 1)) = ((xb.val : ℕ) : ZMod (n + 1)) := ρ.injective e1
    have f2 : ((ya.val : ℕ) : ZMod (n + 1)) = ((yb.val : ℕ) : ZMod (n + 1)) := ρ.injective e2
    have g1 : xa.val = xb.val := by
      have h1' := congrArg ZMod.val f1
      rwa [hv xa (by omega), hv xb (by omega)] at h1'
    have g2 : ya.val = yb.val := by
      have h2' := congrArg ZMod.val f2
      rwa [hv ya (by omega), hv yb (by omega)] at h2'
    rw [show xa = xb from ZMod.val_injective _ g1, show ya = yb from ZMod.val_injective _ g2]
  have hnc' := hncρ _ hA' _ hB' hne'
  have dAB := kChords_disjoint A hA B hB hne
  rw [hAe, hBe] at dAB
  obtain ⟨d1, d2, -, -⟩ := dAB
  have i1 : ρ ((xa.val : ℕ) : ZMod (n + 1)) ≠ ρ ((xb.val : ℕ) : ZMod (n + 1)) := by
    intro he
    apply d1
    rw [hSapp xa hxan, hSapp xb hxbn, he]
  have i2 : ρ ((xa.val : ℕ) : ZMod (n + 1)) ≠ ρ ((yb.val : ℕ) : ZMod (n + 1)) := by
    intro he
    apply d2
    rw [hSapp xa hxan, hSapp yb hybn, he]
  rw [hAe, hBe, hSapp xa hxan, hSapp xb hxbn, hSapp ya hyan, hSapp yb hybn]
  rw [circleIncl_sbtw i1, circleIncl_sbtw i2]
  exact hnc'

/-- Swapping the last two points negates strict betweenness. -/
theorem sbtw_swap23 {N : ℕ} [NeZero N] {a b c : ZMod N} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) :
    sbtw a b c ↔ ¬ sbtw a c b := by
  rw [sbtw_val hab, sbtw_val hac]
  have hne : (b - a).val ≠ (c - a).val := by
    intro he
    apply hbc
    have h1 : b - a = c - a := ZMod.val_injective _ he
    linear_combination h1
  have hlt := ZMod.val_lt (b - a)
  have hlt2 := ZMod.val_lt (c - a)
  omega

/-- Swapping the endpoints of the first chord flips both sides of the non-crossing
condition (for cross-distinct endpoints). -/
theorem nonCross_iff_swap_first {N : ℕ} [NeZero N] {a₁ a₂ b₁ b₂ : ZMod N}
    (h1 : a₁ ≠ b₁) (h2 : a₁ ≠ b₂) (h3 : a₂ ≠ b₁) (h4 : a₂ ≠ b₂) :
    (sbtw a₁ b₁ a₂ ↔ sbtw a₁ b₂ a₂) ↔ (sbtw a₂ b₁ a₁ ↔ sbtw a₂ b₂ a₁) := by
  by_cases haa : a₁ = a₂
  · rw [haa]
  · rw [sbtw_not_reverse h4 h2.symm haa, sbtw_not_reverse h3 h1.symm haa, not_iff_not]

/-- Chords of sum `> n + 1`: reflected to chords of sum `2(n+1) - k < n + 1` via the
parallel structure, hence non-crossing. -/
theorem ExtParallel.nonCross_gt {n : ℕ} {τ : ZMod (n + 1) ≃ ZMod (n + 1)} (hτ : Beautiful τ)
    {c : ZMod (n + 1)} (h : ExtParallel τ c) {k : ℕ} (hk : n + 1 < k) :
    ChordNonCrossing (kChords (InsertNorm τ c) k) := by
  intro A hA B hB hne
  obtain ⟨xa, ya, hsa, hlea, hAe⟩ := mem_kChords.mp hA
  obtain ⟨xb, yb, hsb, hleb, hBe⟩ := mem_kChords.mp hB
  set S := InsertNorm τ c with hSdef
  set q := S topLabel with hqdef
  by_cases hdegA : xa = ya
  · rw [hAe, hdegA]
    exact ⟨fun g => absurd g sbtw_irrefl_left_right,
      fun g => absurd g sbtw_irrefl_left_right⟩
  · by_cases hdegB : xb = yb
    · rw [hBe, hdegB]
    · -- both chords non-degenerate: reflect
      obtain ⟨d1, d2, d3, d4⟩ := kChords_disjoint A hA B hB hne
      rw [hAe, hBe] at d1 d2 d3 d4
      have hrefl := ExtParallel.refl_apply h
      have hval : ∀ x : ZMod (n + 2), (topLabel - x).val = (n + 1) - x.val := by
        intro x
        have e : (topLabel : ZMod (n + 2)) - x = (((n + 1) - x.val : ℕ) : ZMod (n + 2)) := by
          show (((n + 1 : ℕ) : ZMod (n + 2)) - x) = _
          conv_lhs => rw [← ZMod.natCast_zmod_val x]
          rw [← Nat.cast_sub (by have := ZMod.val_lt x; omega : x.val ≤ n + 1)]
        rw [e, ZMod.val_natCast, Nat.mod_eq_of_lt (by have := ZMod.val_lt x; omega :
          (n + 1) - x.val < n + 2)]
      have hk2 : 2 * (n + 1) - k < n + 1 := by
        have h1 := ZMod.val_lt xa
        have h2 := ZMod.val_lt ya
        omega
      have hnc2 := ExtParallel.nonCross_lt hτ (c := c) hk2
      have hsum' : (topLabel - xa).val + (topLabel - ya).val = 2 * (n + 1) - k := by
        rw [hval, hval]
        have h1 := ZMod.val_lt xa
        have h2 := ZMod.val_lt ya
        omega
      have hsum'' : (topLabel - xb).val + (topLabel - yb).val = 2 * (n + 1) - k := by
        rw [hval, hval]
        have h1 := ZMod.val_lt xb
        have h2 := ZMod.val_lt yb
        omega
      have hinj : Function.Injective fun x : ZMod (n + 2) => topLabel - x := by
        intro x y he
        have h2 : topLabel - x = topLabel - y := he
        have h3 : (topLabel - x) - (topLabel - y) = 0 := by rw [h2, sub_self]
        have h5 : (topLabel - x) - (topLabel - y) = y - x := by abel
        rw [h5] at h3
        exact (sub_eq_zero.mp h3).symm
      have hxaxb : xa ≠ xb := by
        intro he
        apply hne
        rw [he] at hsa
        have hyv : ya.val = yb.val := by omega
        rw [hAe, hBe, he, show ya = yb from ZMod.val_injective _ hyv]
      have hyayb : ya ≠ yb := by
        intro he
        apply hne
        rw [← he] at hsb
        have hxv : xa.val = xb.val := by omega
        rw [hAe, hBe, he, show xa = xb from ZMod.val_injective _ hxv]
      have hxayb : xa ≠ yb := fun he => d2 (congrArg S he)
      -- non-crossing of the reflected pair (in our chosen order)
      have hcore : sbtw (q - S xa) (q - S xb) (q - S ya) ↔
          sbtw (q - S xa) (q - S yb) (q - S ya) := by
        rw [← hrefl xa, ← hrefl ya, ← hrefl xb, ← hrefl yb]
        have hA'mem : (S (topLabel - xa), S (topLabel - ya)) ∈ kChords S (2 * (n + 1) - k) ∨
            (S (topLabel - ya), S (topLabel - xa)) ∈ kChords S (2 * (n + 1) - k) := by
          rcases le_or_gt (topLabel - xa).val (topLabel - ya).val with hle | hle
          · exact Or.inl (by rw [mem_kChords]; exact ⟨topLabel - xa, topLabel - ya, hsum',
              hle, rfl⟩)
          · exact Or.inr (by rw [mem_kChords]; exact ⟨topLabel - ya, topLabel - xa, by omega,
              by omega, rfl⟩)
        have hB'mem : (S (topLabel - xb), S (topLabel - yb)) ∈ kChords S (2 * (n + 1) - k) ∨
            (S (topLabel - yb), S (topLabel - xb)) ∈ kChords S (2 * (n + 1) - k) := by
          rcases le_or_gt (topLabel - xb).val (topLabel - yb).val with hle | hle
          · exact Or.inl (by rw [mem_kChords]; exact ⟨topLabel - xb, topLabel - yb, hsum'',
              hle, rfl⟩)
          · exact Or.inr (by rw [mem_kChords]; exact ⟨topLabel - yb, topLabel - xb, by omega,
              by omega, rfl⟩)
        have hne' : (S (topLabel - xa), S (topLabel - ya)) ≠
            (S (topLabel - xb), S (topLabel - yb)) := by
          intro he
          apply hne
          rw [hAe, hBe]
          obtain ⟨g1, g2⟩ := Prod.ext_iff.mp he
          have e1 : xa = xb := hinj (S.injective g1)
          have e2 : ya = yb := hinj (S.injective g2)
          rw [e1, e2]
        have g1 : S (topLabel - xa) ≠ S (topLabel - xb) :=
          fun he => hxaxb (hinj (S.injective he))
        have g2 : S (topLabel - xa) ≠ S (topLabel - yb) :=
          fun he => hxayb (hinj (S.injective he))
        have g3 : S (topLabel - ya) ≠ S (topLabel - xb) :=
          fun he => d3 (congrArg S (hinj (S.injective he)))
        have g4 : S (topLabel - ya) ≠ S (topLabel - yb) :=
          fun he => hyayb (hinj (S.injective he))
        rcases hA'mem with hA'm | hA'm <;> rcases hB'mem with hB'm | hB'm
        · exact hnc2 _ hA'm _ hB'm hne'
        · have h1 := hnc2 _ hA'm _ hB'm (by
            intro he
            obtain ⟨i1, i2⟩ := Prod.ext_iff.mp he
            have e1 : xa = yb := hinj (S.injective i1)
            have e2 : ya = xb := hinj (S.injective i2)
            rw [e1, e2] at hlea
            have hv : yb.val = xb.val := by omega
            exact absurd (ZMod.val_injective _ hv).symm hdegB)
          exact Iff.comm.mp h1
        · have h1 := hnc2 _ hA'm _ hB'm (by
            intro he
            obtain ⟨i1, i2⟩ := Prod.ext_iff.mp he
            have e1 : ya = xb := hinj (S.injective i1)
            have e2 : xa = yb := hinj (S.injective i2)
            rw [e1, e2] at hlea
            rw [← e1, ← e2] at hleb
            have v1 : ya.val = xb.val := congrArg ZMod.val e1
            have v2 : xa.val = yb.val := congrArg ZMod.val e2
            have hv : xa.val = ya.val := by omega
            exact absurd (ZMod.val_injective _ hv) hdegA)
          exact (nonCross_iff_swap_first g1 g2 g3 g4).mpr h1
        · have h1 := hnc2 _ hA'm _ hB'm (by
            intro he
            obtain ⟨i1, i2⟩ := Prod.ext_iff.mp he
            have e1 : ya = yb := hinj (S.injective i1)
            have e2 : xa = xb := hinj (S.injective i2)
            apply hne
            rw [hAe, hBe, e1, e2])
          exact (nonCross_iff_swap_first g1 g2 g3 g4).mpr (Iff.comm.mp h1)
      -- map back via reflection
      have r1 : sbtw (q - S xa) (q - S xb) (q - S ya) ↔ sbtw (S xa) (S ya) (S xb) :=
        (sbtw_reflect (fun he => hdegA (S.injective he)) (show S xa ≠ S xb from d1)
          (show S ya ≠ S xb from d3)).symm
      have r2 : sbtw (q - S xa) (q - S yb) (q - S ya) ↔ sbtw (S xa) (S ya) (S yb) :=
        (sbtw_reflect (fun he => hdegA (S.injective he)) (show S xa ≠ S yb from d2)
          (show S ya ≠ S yb from fun he => hyayb (S.injective he))).symm
      have f1 : sbtw (S xa) (S ya) (S xb) ↔ ¬ sbtw (S xa) (S xb) (S ya) :=
        sbtw_swap23 (fun he => hdegA (S.injective he)) (show S xa ≠ S xb from d1)
          (show S ya ≠ S xb from d3)
      have f2 : sbtw (S xa) (S ya) (S yb) ↔ ¬ sbtw (S xa) (S yb) (S ya) :=
        sbtw_swap23 (fun he => hdegA (S.injective he)) (show S xa ≠ S yb from d2)
          (show S ya ≠ S yb from fun he => hyayb (S.injective he))
      rw [hAe, hBe]
      rw [r1, r2, f1, f2, not_iff_not] at hcore
      exact hcore

/-- The parallel condition implies beauty of the extension: chords of sum `< n + 1`
come from the original arrangement, chords of sum `n + 1` are parallel, and chords
of larger sum reflect to chords of smaller sum. -/
theorem ExtParallel.beautiful {n : ℕ} {τ : ZMod (n + 1) ≃ ZMod (n + 1)} (hτ : Beautiful τ)
    {c : ZMod (n + 1)} (h : ExtParallel τ c) : Beautiful (InsertNorm τ c) := by
  apply beautiful_of_nonCrossing
  intro k
  rcases lt_trichotomy k (n + 1) with hlt | heq | hgt
  · exact ExtParallel.nonCross_lt hτ hlt
  · subst heq
    exact ExtParallel.nonCross_eq h
  · exact ExtParallel.nonCross_gt hτ h hgt
/-- The Type 2 condition of the official solution: the point `0` is aligned with
the `(n+1)`-chords of `τ`. -/
def Type2 {n : ℕ} (τ : ZMod (n + 1) ≃ ZMod (n + 1)) : Prop :=
  ChordAligned (insert (0, 0) (kChords τ (n + 1)))

/-- The position of a label `x` in the inserted arrangement, as a function of the
insertion parameter. -/
theorem InsertNorm_apply {n : ℕ} (τ : ZMod (n + 1) ≃ ZMod (n + 1)) (c x : ZMod (n + 1)) :
    (InsertNorm τ c) (((x.val : ℕ) : ZMod (n + 2))) =
      (((n + 1) - ((rot c τ) 0).val : ℕ) : ZMod (n + 2)) + 1 +
        (((τ x + c).val : ℕ) : ZMod (n + 2)) := by
  have h1 : InsertNorm τ c = Insert (rot c τ)
      (((n + 1) - ((rot c τ) 0).val : ℕ) : ZMod (n + 2)) := rfl
  have h2 : (((x.val : ℕ) : ZMod (n + 2))) ≠ topLabel := by
    intro he
    have h3 : (((x.val : ℕ) : ZMod (n + 2))).val = (topLabel : ZMod (n + 2)).val := by rw [he]
    have hxlt := ZMod.val_lt x
    rw [ZMod.val_cast_of_lt (Nat.lt_succ_of_lt hxlt), topLabel_val] at h3
    omega
  rw [h1, Insert_apply_ne_top (rot c τ) _ h2]
  show circleIncl _ ((rot c τ) ((labelInclEquiv).symm ⟨((x.val : ℕ) : ZMod (n + 2)), h2⟩)) =
    (((n + 1) - ((rot c τ) 0).val : ℕ) : ZMod (n + 2)) + 1 + (((τ x + c).val : ℕ) : ZMod (n + 2))
  rw [show (labelInclEquiv).symm ⟨((x.val : ℕ) : ZMod (n + 2)), h2⟩ =
      ((x.val : ℕ) : ZMod (n + 1)) from by
    show (((((x.val : ℕ) : ZMod (n + 2))).val : ℕ) : ZMod (n + 1)) = _
    rw [ZMod.val_cast_of_lt (Nat.lt_succ_of_lt (ZMod.val_lt x))]]
  show (((n + 1) - ((rot c τ) 0).val : ℕ) : ZMod (n + 2)) + 1 +
      ((((rot c τ) ((x.val : ℕ) : ZMod (n + 1))).val : ℕ) : ZMod (n + 2)) =
    (((n + 1) - ((rot c τ) 0).val : ℕ) : ZMod (n + 2)) + 1 + (((τ x + c).val : ℕ) : ZMod (n + 2))
  rw [rot_apply, rot_apply, show (((x.val : ℕ) : ZMod (n + 1))) = x from by
    rw [ZMod.natCast_zmod_val]]

/-- The parallel condition, restated as a congruence on rotated positions: for
every nonzero label `x`, the rotated positions of `x` and its partner label
`n + 1 - x` sum to `c.val + (n+1)`, or (if `c ≥ 1`) to `c.val - 1`. -/
theorem ExtParallel.star {n : ℕ} {τ : ZMod (n + 1) ≃ ZMod (n + 1)} (hτ0 : τ 0 = 0)
    {c : ZMod (n + 1)} (h : ExtParallel τ c) {x : ZMod (n + 1)} (hx : x ≠ 0) :
    (τ x + c).val + (τ (((n + 1) - x.val : ℕ) : ZMod (n + 1)) + c).val = c.val + (n + 1) ∨
      (1 ≤ c.val ∧
        (τ x + c).val + (τ (((n + 1) - x.val : ℕ) : ZMod (n + 1)) + c).val + 1 = c.val) := by
  have h1 := ExtParallel.refl_apply h (((x.val : ℕ) : ZMod (n + 2)))
  set y : ZMod (n + 1) := (((n + 1) - x.val : ℕ) : ZMod (n + 1)) with hydef
  have hxv : x.val ≠ 0 := by
    intro he
    apply hx
    rw [← ZMod.natCast_zmod_val x, he, Nat.cast_zero]
  have hyv : y.val = (n + 1) - x.val := by
    rw [hydef, ZMod.val_natCast, Nat.mod_eq_of_lt (by have := ZMod.val_lt x; omega :
      (n + 1) - x.val < n + 1)]
  have htop : (topLabel : ZMod (n + 2)) - ((x.val : ℕ) : ZMod (n + 2)) =
      ((y.val : ℕ) : ZMod (n + 2)) := by
    show (((n + 1 : ℕ) : ZMod (n + 2)) - ((x.val : ℕ) : ZMod (n + 2))) = _
    have hxlt := ZMod.val_lt x
    rw [← Nat.cast_sub (by omega : x.val ≤ n + 1), show (n + 1 : ℕ) - x.val = y.val from hyv.symm]
  rw [htop, InsertNorm_apply, InsertNorm_apply] at h1
  have hqt : (InsertNorm τ c) topLabel =
      (((n + 1) - ((rot c τ) 0).val : ℕ) : ZMod (n + 2)) := Insert_top (rot c τ) _
  have hq0 : (rot c τ) 0 = c := by rw [rot_apply, hτ0, zero_add]
  rw [hqt] at h1
  -- h1 : q' + 1 + ↑(τ y + c).val = q' - (q' + 1 + ↑(τ x + c).val) where q' is the cast
  set q : ZMod (n + 2) := (((n + 1) - ((rot c τ) 0).val : ℕ) : ZMod (n + 2)) with hqdef
  have hsum2 : (((q.val + 1 + (τ y + c).val) + (q.val + 1 + (τ x + c).val) : ℕ) :
      ZMod (n + 2)) = q := by
    have e1 : (q + 1 + (((τ y + c).val : ℕ) : ZMod (n + 2))) =
        (((q.val + 1 + (τ y + c).val : ℕ)) : ZMod (n + 2)) := by
      conv_lhs => rw [← ZMod.natCast_zmod_val q, ← Nat.cast_one, ← Nat.cast_add, ← Nat.cast_add]
    have e2 : (q + 1 + (((τ x + c).val : ℕ) : ZMod (n + 2))) =
        (((q.val + 1 + (τ x + c).val : ℕ)) : ZMod (n + 2)) := by
      conv_lhs => rw [← ZMod.natCast_zmod_val q, ← Nat.cast_one, ← Nat.cast_add, ← Nat.cast_add]
    rw [Nat.cast_add, ← e1, ← e2, h1, sub_add_cancel]
  have hqv : q.val = (n + 1) - c.val := by
    rw [hqdef, hq0, ZMod.val_natCast, Nat.mod_eq_of_lt (by have := ZMod.val_lt c; omega :
      (n + 1) - c.val < n + 2)]
  have hclt := ZMod.val_lt c
  have hmod : ((q.val + 1 + (τ y + c).val) + (q.val + 1 + (τ x + c).val)) % (n + 2) =
      q.val := by
    have h1' : ((((q.val + 1 + (τ y + c).val) + (q.val + 1 + (τ x + c).val) : ℕ) :
        ZMod (n + 2))).val = q.val := by rw [hsum2]
    rwa [ZMod.val_natCast] at h1'
  set A := (τ x + c).val + (τ y + c).val with hAdef
  have hBIG' : (q.val + 1 + (τ y + c).val) + (q.val + 1 + (τ x + c).val) =
      A + (2 * (n + 1) + 2 - 2 * c.val) := by
    rw [hqv]
    omega
  rw [hBIG'] at hmod
  rw [hqv] at hmod
  have h1n : 2 * c.val ≤ 2 * n := by omega
  have hA : A ≤ 2 * n := by
    have g1 := ZMod.val_lt (τ x + c)
    have g2 := ZMod.val_lt (τ y + c)
    omega
  set BIG := A + (2 * (n + 1) + 2 - 2 * c.val) with hBIG
  rcases Nat.lt_or_ge BIG (n + 2) with h | h
  · rw [Nat.mod_eq_of_lt h] at hmod
    have hγ' : n + 3 ≤ c.val := by omega
    omega
  · rcases Nat.lt_or_ge BIG (2 * (n + 2)) with h3 | h3
    · have e : BIG = (BIG - (n + 2)) + (n + 2) := by omega
      nth_rewrite 1 [e] at hmod
      rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : BIG - (n + 2) < n + 2)] at hmod
      have hγ1 : 1 ≤ c.val := by omega
      have hA' : A + 1 = c.val := by omega
      exact Or.inr ⟨hγ1, hA'⟩
    · have hB : BIG < 3 * (n + 2) := by
        have e : BIG = (n + 2) * (BIG / (n + 2)) + BIG % (n + 2) := (Nat.div_add_mod _ _).symm
        by_cases hj : 3 ≤ BIG / (n + 2)
        · exfalso
          have hmul : 3 * (n + 2) ≤ (n + 2) * (BIG / (n + 2)) := by
            have h2 := Nat.mul_le_mul_left (n + 2) hj
            omega
          rw [hmod] at e
          omega
        · have hj2 : BIG / (n + 2) ≤ 2 := by omega
          have hmul : (n + 2) * (BIG / (n + 2)) ≤ 2 * (n + 2) := by
            have h2 := Nat.mul_le_mul_left (n + 2) hj2
            omega
          have e2 : BIG = (n + 2) * (BIG / (n + 2)) + BIG % (n + 2) := (Nat.div_add_mod _ _).symm
          rw [hmod] at e2
          omega
      have e : BIG = (BIG - 2 * (n + 2)) + 2 * (n + 2) := by omega
      nth_rewrite 1 [e] at hmod
      rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega : BIG - 2 * (n + 2) < n + 2)]
        at hmod
      have hA' : A = c.val + (n + 1) := by omega
      exact Or.inl hA'

/-- The endpoint-sum of a linear chord with label-sum `n + 1`: it is `n + 1` as a
natural number (the positions of a linear arrangement pair up around the circle). -/
theorem linear_sum_val {n : ℕ} (s : (ZMod (n + 1))ˣ) {x y : ZMod (n + 1)}
    (hsum : x.val + y.val = n + 1) (hx : x ≠ 0) (hy : y ≠ 0) :
    ((s : ZMod (n + 1)) * x).val + ((s : ZMod (n + 1)) * y).val = n + 1 := by
  have h1 := ZMod.val_lt ((s : ZMod (n + 1)) * x)
  have h2 := ZMod.val_lt ((s : ZMod (n + 1)) * y)
  have hmod : (((s : ZMod (n + 1)) * x).val + ((s : ZMod (n + 1)) * y).val) % (n + 1) = 0 := by
    have h3 : ((((s : ZMod (n + 1)) * x).val + ((s : ZMod (n + 1)) * y).val : ℕ) :
        ZMod (n + 1)) = (s : ZMod (n + 1)) * x + (s : ZMod (n + 1)) * y := by
      rw [Nat.cast_add, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    have h4 : (s : ZMod (n + 1)) * x + (s : ZMod (n + 1)) * y = 0 := by
      have h5 : x + y = ((n + 1 : ℕ) : ZMod (n + 1)) := by
        conv_lhs => rw [← ZMod.natCast_zmod_val x, ← ZMod.natCast_zmod_val y, ← Nat.cast_add]
        rw [hsum]
      rw [← mul_add, h5, ZMod.natCast_self, mul_zero]
    have h6 : ((((s : ZMod (n + 1)) * x).val + ((s : ZMod (n + 1)) * y).val : ℕ) :
        ZMod (n + 1)) = 0 := by
      rw [h3, h4]
    have h7 : ((((s : ZMod (n + 1)) * x).val + ((s : ZMod (n + 1)) * y).val : ℕ) :
        ZMod (n + 1)).val = (0 : ZMod (n + 1)).val := by
      rw [h6, ZMod.val_zero]
    rwa [ZMod.val_natCast] at h7
  have hne : ((s : ZMod (n + 1)) * x).val ≠ 0 := by
    intro he
    apply hx
    have h7 : (s : ZMod (n + 1)) * x = 0 := by
      rw [← ZMod.natCast_zmod_val ((s : ZMod (n + 1)) * x), he, Nat.cast_zero]
    have h8 : ((s⁻¹ : (ZMod (n + 1))ˣ) : ZMod (n + 1)) * ((s : ZMod (n + 1)) * x) = 0 := by
      rw [h7, mul_zero]
    rwa [← mul_assoc, show ((s⁻¹ : (ZMod (n + 1))ˣ) : ZMod (n + 1)) * (s : ZMod (n + 1)) = 1 from
      Units.inv_mul s, one_mul] at h8
  have hle : ((s : ZMod (n + 1)) * x).val + ((s : ZMod (n + 1)) * y).val ≤ 2 * n := by omega
  have hj : (((s : ZMod (n + 1)) * x).val + ((s : ZMod (n + 1)) * y).val) / (n + 1) ≤ 1 := by
    have hB : ((s : ZMod (n + 1)) * x).val + ((s : ZMod (n + 1)) * y).val < 2 * (n + 1) := by
      omega
    have h2 : (((s : ZMod (n + 1)) * x).val + ((s : ZMod (n + 1)) * y).val) / (n + 1) < 2 := by
      rw [Nat.div_lt_iff_lt_mul (by omega : 0 < n + 1)]
      exact hB
    omega
  have e : ((s : ZMod (n + 1)) * x).val + ((s : ZMod (n + 1)) * y).val =
      (n + 1) * ((((s : ZMod (n + 1)) * x).val + ((s : ZMod (n + 1)) * y).val) / (n + 1)) +
        (((s : ZMod (n + 1)) * x).val + ((s : ZMod (n + 1)) * y).val) % (n + 1) :=
    (Nat.div_add_mod _ _).symm
  rw [hmod] at e
  interval_cases ((((s : ZMod (n + 1)) * x).val + ((s : ZMod (n + 1)) * y).val) / (n + 1)) <;>
    omega

/-- The val of the lower-circle cast of a non-top label. -/
theorem val_labelIncl {n : ℕ} {x : ZMod (n + 2)} (hx : x ≠ topLabel) :
    (((x.val : ℕ) : ZMod (n + 1))).val = x.val := by
  have h1 : x.val ≠ n + 1 := by
    intro he
    apply hx
    apply ZMod.val_injective (n + 2)
    rw [he, topLabel_val]
  have h2 := ZMod.val_lt x
  exact ZMod.val_cast_of_lt (by omega : x.val < n + 1)

/-- The position of a label in an inserted arrangement, in terms of the rotated
original labelling (auxiliary formula). -/
theorem Insert_apply_of_ne_top {n : ℕ} (τ : ZMod (n + 1) ≃ ZMod (n + 1))
    (q : ZMod (n + 2)) {x : ZMod (n + 2)} (hx : x ≠ topLabel) :
    Insert τ q x = q + 1 + (((τ ((x.val : ℕ) : ZMod (n + 1))).val : ℕ) : ZMod (n + 2)) := by
  rw [Insert_apply_ne_top τ q hx]
  show circleIncl q (τ ((labelInclEquiv).symm ⟨x, hx⟩)) = _
  rw [show (labelInclEquiv).symm ⟨x, hx⟩ = ((x.val : ℕ) : ZMod (n + 1)) from rfl]
  rfl

/-- For a linear labelling, insertion at `c = 0` appends the new label at the end,
giving the linear arrangement of `[0, n+1]`: parallel. -/
theorem lin_valid_zero {n : ℕ} (hn : 2 ≤ n) {τ : ZMod (n + 1) ≃ ZMod (n + 1)}
    (hτ : Linear τ) : ExtParallel τ 0 := by
  obtain ⟨s, hs⟩ := hτ
  intro A hA
  obtain ⟨a, b, hsum, hle, hAe⟩ := mem_kChords.mp hA
  have hS : InsertNorm τ 0 = Insert τ ((n + 1 : ℕ) : ZMod (n + 2)) := by
    show Insert (rot 0 τ) (((n + 1) - ((rot 0 τ) 0).val : ℕ) : ZMod (n + 2)) = _
    rw [rot_zero, hs 0, mul_zero, ZMod.val_zero, Nat.sub_zero]
  have hq' : (InsertNorm τ 0) topLabel = ((n + 1 : ℕ) : ZMod (n + 2)) := by
    rw [hS, Insert_top]
  rw [hAe, hq']
  by_cases ha : a = 0
  · subst ha
    have hb : b = topLabel := by
      apply ZMod.val_injective (n + 2)
      rw [ZMod.val_zero] at hsum
      rw [topLabel_val]
      omega
    rw [hb, InsertNorm_zero, hq', zero_add]
  · have han : a ≠ topLabel := by
      intro he
      rw [he, topLabel_val] at hsum hle
      omega
    have hbn : b ≠ topLabel := by
      intro he
      apply ha
      apply ZMod.val_injective (n + 2)
      rw [he, topLabel_val] at hsum
      rw [ZMod.val_zero]
      omega
    have ha0 : ((a.val : ℕ) : ZMod (n + 1)) ≠ 0 := by
      intro he
      have h1 : (((a.val : ℕ) : ZMod (n + 1))).val = (0 : ZMod (n + 1)).val := by rw [he]
      rw [val_labelIncl han, ZMod.val_zero] at h1
      exact ha (ZMod.val_injective _ (by rw [h1, ZMod.val_zero]))
    have hb0 : ((b.val : ℕ) : ZMod (n + 1)) ≠ 0 := by
      intro he
      have h1 : (((b.val : ℕ) : ZMod (n + 1))).val = (0 : ZMod (n + 1)).val := by rw [he]
      rw [val_labelIncl hbn, ZMod.val_zero] at h1
      have h2 : a = topLabel := by
        apply ZMod.val_injective (n + 2)
        rw [topLabel_val]
        omega
      exact han h2
    have hvv : (τ ((a.val : ℕ) : ZMod (n + 1))).val + (τ ((b.val : ℕ) : ZMod (n + 1))).val =
        n + 1 := by
      have e1 : (s : ZMod (n + 1)) * ((a.val : ℕ) : ZMod (n + 1)) =
          τ ((a.val : ℕ) : ZMod (n + 1)) := (hs _).symm
      have e2 : (s : ZMod (n + 1)) * ((b.val : ℕ) : ZMod (n + 1)) =
          τ ((b.val : ℕ) : ZMod (n + 1)) := (hs _).symm
      rw [← e1, ← e2]
      apply linear_sum_val s _ ha0 hb0
      rw [val_labelIncl han, val_labelIncl hbn]
      exact hsum
    rw [hS, Insert_apply_of_ne_top τ _ han, Insert_apply_of_ne_top τ _ hbn, hs, hs]
    show ((↑(n + 1 : ℕ) + 1 + (((↑s : ZMod (n + 1)) * ((a.val : ℕ) : ZMod (n + 1))).val : ℕ) :
        ZMod (n + 2)) + (↑(n + 1 : ℕ) + 1 +
        (((↑s : ZMod (n + 1)) * ((b.val : ℕ) : ZMod (n + 1))).val : ℕ) : ZMod (n + 2)) :
        ZMod (n + 2)) = ((n + 1 : ℕ) : ZMod (n + 2))
    rw [show (↑s : ZMod (n + 1)) * ((a.val : ℕ) : ZMod (n + 1)) =
        τ ((a.val : ℕ) : ZMod (n + 1)) from (hs _).symm,
      show (↑s : ZMod (n + 1)) * ((b.val : ℕ) : ZMod (n + 1)) =
        τ ((b.val : ℕ) : ZMod (n + 1)) from (hs _).symm]
    have e7 : (↑(n + 1 : ℕ) + 1 + ((τ ((a.val : ℕ) : ZMod (n + 1))).val : ℕ) : ZMod (n + 2)) +
        (↑(n + 1 : ℕ) + 1 + ((τ ((b.val : ℕ) : ZMod (n + 1))).val : ℕ) : ZMod (n + 2)) =
        (((2 * (n + 1) + 2 + ((τ ((a.val : ℕ) : ZMod (n + 1))).val +
          (τ ((b.val : ℕ) : ZMod (n + 1))).val) : ℕ)) : ZMod (n + 2)) := by
      push_cast
      ring
    rw [e7, hvv]
    show (((2 * (n + 1) + 2 + (n + 1) : ℕ)) : ZMod (n + 2)) = _
    have e6 : 2 * (n + 1) + 2 + (n + 1) = (n + 1) + 2 * (n + 2) := by omega
    rw [e6, Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, mul_zero, add_zero]

/-- For a linear labelling, insertion at `c = -1` prepends the new label at the
beginning: also parallel. -/
theorem lin_valid_neg {n : ℕ} (hn : 2 ≤ n) {τ : ZMod (n + 1) ≃ ZMod (n + 1)}
    (hτ : Linear τ) : ExtParallel τ (-1) := by
  obtain ⟨s, hs⟩ := hτ
  intro A hA
  obtain ⟨a, b, hsum, hle, hAe⟩ := mem_kChords.mp hA
  have hS : InsertNorm τ (-1) = Insert (rot (-1) τ) ((1 : ℕ) : ZMod (n + 2)) := by
    show Insert (rot (-1) τ) (((n + 1) - ((rot (-1) τ) 0).val : ℕ) : ZMod (n + 2)) = _
    rw [rot_apply, hs 0, mul_zero, zero_add]
    haveI : Fact (1 < n + 1) := ⟨by omega⟩
    have e : ((-1 : ZMod (n + 1))).val = n := by
      have h1 : (1 : ZMod (n + 1)) ≠ 0 := by
        intro h2
        have h3 : (1 : ZMod (n + 1)).val = (0 : ZMod (n + 1)).val := by rw [h2]
        rw [ZMod.val_one, ZMod.val_zero] at h3
        omega
      rw [val_neg'' h1, ZMod.val_one, Nat.add_sub_cancel]
    rw [e, show (n + 1) - n = 1 from by omega]
  have hq' : (InsertNorm τ (-1)) topLabel = ((1 : ℕ) : ZMod (n + 2)) := by
    rw [hS, Insert_top]
  rw [hAe, hq']
  by_cases ha : a = 0
  · subst ha
    have hb : b = topLabel := by
      apply ZMod.val_injective (n + 2)
      rw [ZMod.val_zero] at hsum
      rw [topLabel_val]
      omega
    rw [hb, InsertNorm_zero, hq', zero_add]
  · have han : a ≠ topLabel := by
      intro he
      rw [he, topLabel_val] at hsum hle
      omega
    have hbn : b ≠ topLabel := by
      intro he
      apply ha
      apply ZMod.val_injective (n + 2)
      rw [he, topLabel_val] at hsum
      rw [ZMod.val_zero]
      omega
    have ha0 : ((a.val : ℕ) : ZMod (n + 1)) ≠ 0 := by
      intro he
      have h1 : (((a.val : ℕ) : ZMod (n + 1))).val = (0 : ZMod (n + 1)).val := by rw [he]
      rw [val_labelIncl han, ZMod.val_zero] at h1
      exact ha (ZMod.val_injective _ (by rw [h1, ZMod.val_zero]))
    have hb0 : ((b.val : ℕ) : ZMod (n + 1)) ≠ 0 := by
      intro he
      have h1 : (((b.val : ℕ) : ZMod (n + 1))).val = (0 : ZMod (n + 1)).val := by rw [he]
      rw [val_labelIncl hbn, ZMod.val_zero] at h1
      have h2 : a = topLabel := by
        apply ZMod.val_injective (n + 2)
        rw [topLabel_val]
        omega
      exact han h2
    -- positions: nonzero label x sits at ((s * x).val - 1) + 2
    have happ : ∀ x : ZMod (n + 2), x ≠ topLabel → x ≠ 0 → (InsertNorm τ (-1)) x =
        ((1 : ℕ) : ZMod (n + 2)) + 1 +
          ((((s : ZMod (n + 1)) * ((x.val : ℕ) : ZMod (n + 1))).val - 1 : ℕ) : ZMod (n + 2)) := by
      intro x hx hx0
      have h1 := hS
      rw [h1, Insert_apply_ne_top (rot (-1) τ) _ hx]
      show circleIncl _ ((rot (-1) τ) ((labelInclEquiv).symm ⟨x, hx⟩)) = _
      rw [(show (labelInclEquiv).symm ⟨x, hx⟩ = ((x.val : ℕ) : ZMod (n + 1)) from rfl), rot_apply,
        hs]
      show ((1 : ℕ) : ZMod (n + 2)) + 1 +
          ((((s : ZMod (n + 1)) * ((x.val : ℕ) : ZMod (n + 1)) + (-1 : ZMod (n + 1))).val : ℕ) :
            ZMod (n + 2)) = _
      have e1 : (s : ZMod (n + 1)) * ((x.val : ℕ) : ZMod (n + 1)) + (-1 : ZMod (n + 1)) =
          (s : ZMod (n + 1)) * ((x.val : ℕ) : ZMod (n + 1)) - 1 := by ring
      rw [e1]
      have e2 : (((s : ZMod (n + 1)) * ((x.val : ℕ) : ZMod (n + 1)) - 1).val : ℕ) =
          ((s : ZMod (n + 1)) * ((x.val : ℕ) : ZMod (n + 1))).val - 1 := by
        have hpos : (s : ZMod (n + 1)) * ((x.val : ℕ) : ZMod (n + 1)) ≠ 0 := by
          intro he
          apply hx0
          have h9 : ((x.val : ℕ) : ZMod (n + 1)) = 0 := by
            have h10 : ((s⁻¹ : (ZMod (n + 1))ˣ) : ZMod (n + 1)) *
                ((s : ZMod (n + 1)) * ((x.val : ℕ) : ZMod (n + 1))) = 0 := by
              rw [he, mul_zero]
            rwa [← mul_assoc, show ((s⁻¹ : (ZMod (n + 1))ˣ) : ZMod (n + 1)) *
                (s : ZMod (n + 1)) = 1 from Units.inv_mul s, one_mul] at h10
          have h11 : (((x.val : ℕ) : ZMod (n + 1))).val = (0 : ZMod (n + 1)).val := by rw [h9]
          have h12 := ZMod.val_lt x
          have h13 : (((x.val : ℕ) : ZMod (n + 1))).val = x.val := val_labelIncl hx
          rw [h13, ZMod.val_zero] at h11
          apply ZMod.val_injective (n + 2)
          rw [h11, ZMod.val_zero]
        have h11 : ((s : ZMod (n + 1)) * ((x.val : ℕ) : ZMod (n + 1))).val ≠ 0 := by
          intro he2
          apply hpos
          rw [← ZMod.natCast_zmod_val ((s : ZMod (n + 1)) * ((x.val : ℕ) : ZMod (n + 1))), he2,
            Nat.cast_zero]
        have e3 : ((s : ZMod (n + 1)) * ((x.val : ℕ) : ZMod (n + 1)) - 1) =
            ((((s : ZMod (n + 1)) * ((x.val : ℕ) : ZMod (n + 1))).val - 1 : ℕ) :
              ZMod (n + 1)) := by
          have h13 : (s : ZMod (n + 1)) * ((x.val : ℕ) : ZMod (n + 1)) - 1 =
              (((s : ZMod (n + 1)) * ((x.val : ℕ) : ZMod (n + 1))).val : ℕ) -
                (1 : ZMod (n + 1)) := by
            conv_lhs => rw [← ZMod.natCast_zmod_val ((s : ZMod (n + 1)) *
              ((x.val : ℕ) : ZMod (n + 1)))]
          rw [h13, Nat.cast_sub (by omega : 1 ≤
            ((s : ZMod (n + 1)) * ((x.val : ℕ) : ZMod (n + 1))).val), Nat.cast_one]
        rw [e3]
        have h12 := ZMod.val_lt ((s : ZMod (n + 1)) * ((x.val : ℕ) : ZMod (n + 1)))
        rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega :
          ((s : ZMod (n + 1)) * ((x.val : ℕ) : ZMod (n + 1))).val - 1 < n + 1)]
      rw [e2]
    have hsumval : (((s : ZMod (n + 1)) * ((a.val : ℕ) : ZMod (n + 1))).val - 1) +
        (((s : ZMod (n + 1)) * ((b.val : ℕ) : ZMod (n + 1))).val - 1) + 2 + 2 = 1 + (n + 2) := by
      have hv := linear_sum_val s (by rw [val_labelIncl han, val_labelIncl hbn]; exact hsum)
        ha0 hb0
      have hpos1 : ((s : ZMod (n + 1)) * ((a.val : ℕ) : ZMod (n + 1))).val ≠ 0 := by
        intro he
        apply ha0
        have h7 : (s : ZMod (n + 1)) * ((a.val : ℕ) : ZMod (n + 1)) = 0 := by
          rw [← ZMod.natCast_zmod_val ((s : ZMod (n + 1)) * ((a.val : ℕ) : ZMod (n + 1))), he,
            Nat.cast_zero]
        have h8 : ((s⁻¹ : (ZMod (n + 1))ˣ) : ZMod (n + 1)) *
            ((s : ZMod (n + 1)) * ((a.val : ℕ) : ZMod (n + 1))) = 0 := by
          rw [h7, mul_zero]
        rwa [← mul_assoc, show ((s⁻¹ : (ZMod (n + 1))ˣ) : ZMod (n + 1)) *
            (s : ZMod (n + 1)) = 1 from Units.inv_mul s, one_mul] at h8
      have hpos2 : ((s : ZMod (n + 1)) * ((b.val : ℕ) : ZMod (n + 1))).val ≠ 0 := by
        intro he
        apply hb0
        have h7 : (s : ZMod (n + 1)) * ((b.val : ℕ) : ZMod (n + 1)) = 0 := by
          rw [← ZMod.natCast_zmod_val ((s : ZMod (n + 1)) * ((b.val : ℕ) : ZMod (n + 1))), he,
            Nat.cast_zero]
        have h8 : ((s⁻¹ : (ZMod (n + 1))ˣ) : ZMod (n + 1)) *
            ((s : ZMod (n + 1)) * ((b.val : ℕ) : ZMod (n + 1))) = 0 := by
          rw [h7, mul_zero]
        rwa [← mul_assoc, show ((s⁻¹ : (ZMod (n + 1))ˣ) : ZMod (n + 1)) *
            (s : ZMod (n + 1)) = 1 from Units.inv_mul s, one_mul] at h8
      omega
    rw [happ a han (fun he => ha0 (by rw [he, ZMod.val_zero, Nat.cast_zero])),
      happ b hbn (fun he => hb0 (by rw [he, ZMod.val_zero, Nat.cast_zero]))]
    have e5 : (((1 : ℕ) : ZMod (n + 2)) + 1 +
        ((((s : ZMod (n + 1)) * ((a.val : ℕ) : ZMod (n + 1))).val - 1 : ℕ) : ZMod (n + 2))) +
        (((1 : ℕ) : ZMod (n + 2)) + 1 +
        ((((s : ZMod (n + 1)) * ((b.val : ℕ) : ZMod (n + 1))).val - 1 : ℕ) : ZMod (n + 2))) =
        (((((s : ZMod (n + 1)) * ((a.val : ℕ) : ZMod (n + 1))).val - 1) +
          (((s : ZMod (n + 1)) * ((b.val : ℕ) : ZMod (n + 1))).val - 1) + 2 + 2 : ℕ) :
          ZMod (n + 2)) := by
      push_cast
      ring
    rw [e5, hsumval, Nat.cast_add, ZMod.natCast_self, add_zero]

/-- A linear labelling has only the two obvious parallel extensions: the insertion
parameter must be `0` or `-1`. -/
theorem lin_unique {n : ℕ} (hn : 2 ≤ n) {τ : ZMod (n + 1) ≃ ZMod (n + 1)}
    (hτ : Beautiful τ) (hτ0 : τ 0 = 0) (hτl : Linear τ) {c : ZMod (n + 1)}
    (h : ExtParallel τ c) : c = 0 ∨ c = -1 := by
  obtain ⟨s, hs⟩ := hτl
  have hstar := ExtParallel.star hτ0 h (x := τ.symm 1) (by
    intro he
    have h1 : τ (τ.symm 1) = τ 0 := by rw [he, hτ0]
    have h2 : τ (τ.symm 1) = 1 := Equiv.apply_symm_apply τ 1
    rw [h1, hτ0] at h2
    haveI : Fact (1 < n + 1) := ⟨by omega⟩
    have h3 : (1 : ZMod (n + 1)).val = (0 : ZMod (n + 1)).val := by rw [← h2]
    rw [ZMod.val_one, ZMod.val_zero] at h3
    omega)
  -- compute the two rotated positions
  have hτ1 : τ (τ.symm 1) = 1 := Equiv.apply_symm_apply τ 1
  have hx1 : (τ (τ.symm 1) + c).val = (1 + c.val) % (n + 1) := by
    have e : τ (τ.symm 1) + c = ((1 + c.val : ℕ) : ZMod (n + 1)) := by
      rw [hτ1]
      show (1 + c : ZMod (n + 1)) = _
      conv_lhs => rw [← ZMod.natCast_zmod_val c]
      rw [Nat.cast_add, Nat.cast_one]
    rw [e, ZMod.val_natCast]
  have hy1 : τ (((n + 1) - (τ.symm 1).val : ℕ) : ZMod (n + 1)) = -1 := by
    have h5 : (((n + 1) - (τ.symm 1).val : ℕ) : ZMod (n + 1)) = -(τ.symm 1) := by
      rw [eq_neg_iff_add_eq_zero]
      have h6 : (((n + 1 : ℕ) - (τ.symm 1).val : ℕ) : ZMod (n + 1)) +
          ((τ.symm 1 : ZMod (n + 1))) = 0 := by
        have h5 : (((n + 1 : ℕ) - (τ.symm 1).val : ℕ) : ZMod (n + 1)) +
            (((τ.symm 1).val : ℕ) : ZMod (n + 1)) = 0 := by
          rw [← Nat.cast_add, show (n + 1 : ℕ) - (τ.symm 1).val + (τ.symm 1).val = n + 1 from by
            have h7 := ZMod.val_lt (τ.symm 1)
            omega, ZMod.natCast_self]
        rw [show (((τ.symm 1).val : ℕ) : ZMod (n + 1)) = τ.symm 1 from ZMod.natCast_zmod_val _] at h5
        exact h5
      exact h6
    rw [h5, hs _, mul_neg, ← hs (τ.symm 1), hτ1]
  have hy2 : (τ (((n + 1) - (τ.symm 1).val : ℕ) : ZMod (n + 1)) + c).val =
      (c.val + n) % (n + 1) := by
    have e : τ (((n + 1) - (τ.symm 1).val : ℕ) : ZMod (n + 1)) + c = c - 1 := by
      rw [hy1]
      ring
    rw [e]
    have e2 : (c - 1).val = (c.val + n) % (n + 1) := by
      have e3 : c - 1 = ((c.val + n : ℕ) : ZMod (n + 1)) := by
        have e4 : ((c.val : ℕ) : ZMod (n + 1)) = ((c.val + (n + 1) : ℕ) : ZMod (n + 1)) := by
          rw [Nat.cast_add, ZMod.natCast_self, add_zero]
        conv_lhs => rw [← ZMod.natCast_zmod_val c]
        rw [e4, show (1 : ZMod (n + 1)) = ((1 : ℕ) : ZMod (n + 1)) from by rw [Nat.cast_one],
          ← Nat.cast_sub (by omega : 1 ≤ c.val + (n + 1)),
          show c.val + (n + 1) - 1 = c.val + n from by omega]
      rw [e3, ZMod.val_natCast]
    exact e2
  rw [hx1, hy2] at hstar
  -- case analysis on c.val
  have hclt := ZMod.val_lt c
  by_cases h0 : c.val = 0
  · left
    apply ZMod.val_injective (n + 1)
    rw [h0, ZMod.val_zero]
  · by_cases hcn : c.val = n
    · right
      apply ZMod.val_injective (n + 1)
      rw [hcn]
      have e : ((-1 : ZMod (n + 1))).val = n := by
        have h1 : (-1 : ZMod (n + 1)) = ((n : ℕ) : ZMod (n + 1)) := by
          rw [neg_eq_iff_add_eq_zero,
            show (1 : ZMod (n + 1)) = ((1 : ℕ) : ZMod (n + 1)) from by rw [Nat.cast_one],
            ← Nat.cast_add, show 1 + n = n + 1 from by omega, ZMod.natCast_self]
        rw [h1, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega : n < n + 1)]
      exact e.symm
    · -- 1 ≤ c.val ≤ n - 1: derive a contradiction
      have hsum1 : (1 + c.val) % (n + 1) = 1 + c.val :=
        Nat.mod_eq_of_lt (by omega : 1 + c.val < n + 1)
      have hsum2 : (c.val + n) % (n + 1) = c.val - 1 := by
        have e : c.val + n = (c.val - 1) + (n + 1) := by omega
        rw [e, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : c.val - 1 < n + 1)]
      rw [hsum1, hsum2] at hstar
      rcases hstar with h1 | ⟨h1, h2⟩
      · omega
      · omega
/-- In a beautiful labelling with `0` fixed, the `n`-chords have constant endpoint
sum `τ n`: for every label `x`, `τ x + τ (n - x) = τ n`. This is the "second
parallel family" of the official solution's Type 2 analysis; it needs only beauty,
not the Type 2 assumption. -/
theorem sum_kChords_n {n : ℕ} (hn : 2 ≤ n) {τ : ZMod (n + 1) ≃ ZMod (n + 1)}
    (hτ : Beautiful τ) (hτ0 : τ 0 = 0) (x : ZMod (n + 1)) :
    τ x + τ ((n : ZMod (n + 1)) - x) = τ n := by
  haveI : NeZero (n + 1) := ⟨by omega⟩
  have hcov : ∀ p : ZMod (n + 1), ∃ A ∈ kChords τ n, p = A.1 ∨ p = A.2 := by
    intro p
    set x₀ := τ.symm p with hx₀
    set y₀ := ((n - x₀.val : ℕ) : ZMod (n + 1)) with hy₀
    have hy₀v : y₀.val = n - x₀.val := by
      rw [hy₀, ZMod.val_natCast, Nat.mod_eq_of_lt (by have h := ZMod.val_lt x₀; omega :
        n - x₀.val < n + 1)]
    have hx₀v : x₀.val ≤ n := by have h := ZMod.val_lt x₀; omega
    have hsum : x₀.val + y₀.val = n := by omega
    have hpx : τ x₀ = p := Equiv.apply_symm_apply τ p
    by_cases hxy : x₀.val ≤ y₀.val
    · exact ⟨(τ x₀, τ y₀), mem_kChords.2 ⟨x₀, y₀, hsum, hxy, rfl⟩, Or.inl hpx.symm⟩
    · exact ⟨(τ y₀, τ x₀), mem_kChords.2 ⟨y₀, x₀, by omega, by omega, rfl⟩,
        Or.inr hpx.symm⟩
  have hdeg : ∀ A ∈ kChords τ n, ∀ B ∈ kChords τ n, A.1 = A.2 → B.1 = B.2 → A = B := by
    intro A hA B hB hAA hBB
    rw [mem_kChords] at hA hB
    obtain ⟨xa, ya, hsa, hlea, rfl⟩ := hA
    obtain ⟨xb, yb, hsb, hleb, rfl⟩ := hB
    have hxa : xa = ya := τ.injective hAA
    have hxb : xb = yb := τ.injective hBB
    have hvva : xa.val = ya.val := by rw [hxa]
    have hvvb : xb.val = yb.val := by rw [hxb]
    have hv : xa.val = xb.val := by omega
    have hxx : xa = xb := ZMod.val_injective _ hv
    have hyy : ya = yb := by rw [← hxa, hxx, hxb]
    rw [hxx, hyy]
  obtain ⟨c₁, hc₁⟩ := const_sum_of_aligned (kChords τ n)
    (Beautiful.kChords_nonCrossing hτ n) kChords_disjoint
    (aligned_kChords (n + 1) τ hτ n) hcov hdeg
  have hchord0 : (τ 0, τ (n : ZMod (n + 1))) ∈ kChords τ n := by
    rw [mem_kChords]
    refine ⟨0, (n : ZMod (n + 1)), ?_, Nat.zero_le _, rfl⟩
    rw [ZMod.val_zero, ZMod.val_natCast, Nat.mod_eq_of_lt (Nat.lt_succ_self n), zero_add]
  have hc₁v : c₁ = τ n := by
    have h := hc₁ (τ 0, τ (n : ZMod (n + 1))) hchord0
    rw [show (τ 0, τ (n : ZMod (n + 1))).1 + (τ 0, τ (n : ZMod (n + 1))).2 =
        τ 0 + τ (n : ZMod (n + 1)) from rfl, hτ0, zero_add] at h
    exact h.symm
  set y := ((n - x.val : ℕ) : ZMod (n + 1)) with hy
  have hyv : y.val = n - x.val := by
    rw [hy, ZMod.val_natCast, Nat.mod_eq_of_lt (by have h := ZMod.val_lt x; omega :
      n - x.val < n + 1)]
  have hxv : x.val ≤ n := by have h := ZMod.val_lt x; omega
  have hye : y = (n : ZMod (n + 1)) - x := by
    rw [hy]
    conv_rhs => rw [← ZMod.natCast_zmod_val x]
    rw [← Nat.cast_sub hxv]
  by_cases hxy : x.val ≤ y.val
  · have hmem : (τ x, τ y) ∈ kChords τ n := mem_kChords.2 ⟨x, y, by omega, hxy, rfl⟩
    have h := hc₁ _ hmem
    rw [show (τ x, τ y).1 + (τ x, τ y).2 = τ x + τ y from rfl, hc₁v, hye] at h
    exact h
  · have hmem : (τ y, τ x) ∈ kChords τ n := mem_kChords.2 ⟨y, x, by omega, by omega, rfl⟩
    have h := hc₁ _ hmem
    rw [show (τ y, τ x).1 + (τ y, τ x).2 = τ y + τ x from rfl, hc₁v, hye,
      add_comm (τ ((n : ZMod (n + 1)) - x)) (τ x)] at h
    exact h

/-- The Type 2 recursion: from the two parallel-family relations
`τ x + τ (-x) = 0` and `τ x + τ (n - x) = τ n`, the labelling `τ` is given by
multiplication by the unit `-τ n`. -/
theorem linear_of_two_sums {n : ℕ} (hn : 2 ≤ n) {τ : ZMod (n + 1) ≃ ZMod (n + 1)}
    (hτ0 : τ 0 = 0)
    (R1 : ∀ x : ZMod (n + 1), τ x + τ (-x) = 0)
    (R2 : ∀ x : ZMod (n + 1), τ x + τ ((n : ZMod (n + 1)) - x) = τ n) :
    Linear τ := by
  haveI : NeZero (n + 1) := ⟨by omega⟩
  have hn1 : ((n : ℕ) : ZMod (n + 1)) = -1 := by
    have h := ZMod.natCast_self (n + 1)
    rw [show ((n + 1 : ℕ) : ZMod (n + 1)) = (n : ZMod (n + 1)) + 1 from by
      push_cast; ring] at h
    rw [eq_neg_iff_add_eq_zero]
    exact h
  have step : ∀ x : ZMod (n + 1), τ (x + 1) = τ x - τ (n : ZMod (n + 1)) := by
    intro x
    have h1 := R1 (x + 1)
    have h2 := R2 x
    have h3 : (-(x + 1) : ZMod (n + 1)) = (n : ZMod (n + 1)) - x := by
      rw [hn1]
      ring
    rw [h3] at h1
    linear_combination h1 - h2
  have hInd : ∀ k : ℕ, τ (k : ZMod (n + 1)) =
      -((k : ℕ) : ZMod (n + 1)) * τ (n : ZMod (n + 1)) := by
    intro k
    induction k with
    | zero => rw [Nat.cast_zero, neg_zero, zero_mul, hτ0]
    | succ k ih =>
      rw [Nat.cast_succ, step, ih]
      ring
  have hForm : ∀ x : ZMod (n + 1), τ x = -x * τ (n : ZMod (n + 1)) := by
    intro x
    conv_lhs => rw [← ZMod.natCast_zmod_val x]
    rw [hInd x.val, ZMod.natCast_zmod_val x]
  have hForm' : ∀ x : ZMod (n + 1), τ x = (-τ (n : ZMod (n + 1))) * x := by
    intro x
    rw [hForm x]
    ring
  have h1 : (-τ (n : ZMod (n + 1))) * (τ.symm 1) = 1 := by
    rw [← hForm' (τ.symm 1), Equiv.apply_symm_apply]
  obtain ⟨u, hu⟩ := IsUnit.of_mul_eq_one _ h1
  exact ⟨u, fun x => by rw [hForm' x, hu]⟩

/-- In a Type 2 beautiful labelling, the `(n+1)`-chords together with the
degenerate chord `{0, 0}` have constant endpoint sum `0`: for every label `x`,
`τ x + τ (-x) = 0`. This is the "first parallel family" of the official
solution's Type 2 analysis. When `n` is odd there is a second degenerate chord
(the antipodal pair of `{0, 0}`), and the two-degenerate structure theorem is
needed. -/
theorem sum_kChords_succ_of_type2 {n : ℕ} (hn : 2 ≤ n) {τ : ZMod (n + 1) ≃ ZMod (n + 1)}
    (hτ : Beautiful τ) (hτ0 : τ 0 = 0) (hT : Type2 τ) (x : ZMod (n + 1)) :
    τ x + τ (-x) = 0 := by
  haveI : NeZero (n + 1) := ⟨by omega⟩
  set F1 := insert (0, 0) (kChords τ (n + 1)) with hF1
  have hT' : ChordAligned F1 := hT
  have hnc : ChordNonCrossing F1 := by
    intro A hA B hB hne
    rw [hF1, Finset.mem_insert] at hA hB
    rcases hA with rfl | hA
    · exact ⟨fun h => absurd h sbtw_irrefl_left_right,
        fun h => absurd h sbtw_irrefl_left_right⟩
    · rcases hB with rfl | hB
      · exact Iff.rfl
      · exact Beautiful.kChords_nonCrossing hτ (n + 1) A hA B hB hne
  have hdj : ChordDisjoint F1 := by
    intro A hA B hB hne
    rw [hF1, Finset.mem_insert] at hA hB
    rcases hA with rfl | hA
    · rcases hB with rfl | hB
      · exact absurd rfl hne
      · obtain ⟨u, v, hsumu, hleu, hBe⟩ := mem_kChords.mp hB
        rw [hBe]
        have huv : u ≠ 0 := by
          intro he
          have h1 : u.val = 0 := by rw [he, ZMod.val_zero]
          have h2 := ZMod.val_lt v
          omega
        have hvv : v ≠ 0 := by
          intro he
          have h1 : v.val = 0 := by rw [he, ZMod.val_zero]
          have h2 := ZMod.val_lt u
          omega
        have hu0 : τ u ≠ 0 := by
          intro he
          apply huv
          have h3 : u = 0 := τ.injective (by rw [he, hτ0])
          exact h3
        have hv0 : τ v ≠ 0 := by
          intro he
          apply hvv
          have h3 : v = 0 := τ.injective (by rw [he, hτ0])
          exact h3
        exact ⟨fun h => hu0 h.symm, fun h => hv0 h.symm,
          fun h => hu0 h.symm, fun h => hv0 h.symm⟩
    · rcases hB with rfl | hB
      · obtain ⟨u, v, hsumu, hleu, hAe⟩ := mem_kChords.mp hA
        rw [hAe]
        have huv : u ≠ 0 := by
          intro he
          have h1 : u.val = 0 := by rw [he, ZMod.val_zero]
          have h2 := ZMod.val_lt v
          omega
        have hvv : v ≠ 0 := by
          intro he
          have h1 : v.val = 0 := by rw [he, ZMod.val_zero]
          have h2 := ZMod.val_lt u
          omega
        have hu0 : τ u ≠ 0 := by
          intro he
          apply huv
          have h3 : u = 0 := τ.injective (by rw [he, hτ0])
          exact h3
        have hv0 : τ v ≠ 0 := by
          intro he
          apply hvv
          have h3 : v = 0 := τ.injective (by rw [he, hτ0])
          exact h3
        exact ⟨hu0, hu0, fun h => hv0 h, fun h => hv0 h⟩
      · exact kChords_disjoint A hA B hB hne
  have hcov : ∀ p : ZMod (n + 1), ∃ A ∈ F1, p = A.1 ∨ p = A.2 := by
    intro p
    by_cases hp0 : p = 0
    · refine ⟨(0, 0), ?_, Or.inl ?_⟩
      · rw [hF1]
        exact Finset.mem_insert_self _ _
      · rw [hp0]
    · set x₀ := τ.symm p with hx₀
      have hx₀0 : x₀ ≠ 0 := by
        intro he
        apply hp0
        have h1 : τ x₀ = p := Equiv.apply_symm_apply τ p
        rw [he, hτ0] at h1
        exact h1.symm
      have hx₀v : 1 ≤ x₀.val := by
        by_contra h0
        have hz : x₀.val = 0 := by omega
        apply hx₀0
        have e := ZMod.natCast_zmod_val x₀
        rw [hz, Nat.cast_zero] at e
        exact e.symm
      set y₀ := ((n + 1 - x₀.val : ℕ) : ZMod (n + 1)) with hy₀
      have hy₀v : y₀.val = n + 1 - x₀.val := by
        rw [hy₀, ZMod.val_natCast, Nat.mod_eq_of_lt (by have h := ZMod.val_lt x₀; omega :
          n + 1 - x₀.val < n + 1)]
      have hsum : x₀.val + y₀.val = n + 1 := by have h := ZMod.val_lt x₀; omega
      have hpx : τ x₀ = p := Equiv.apply_symm_apply τ p
      by_cases hxy : x₀.val ≤ y₀.val
      · refine ⟨(τ x₀, τ y₀), ?_, Or.inl hpx.symm⟩
        rw [hF1]
        exact Finset.mem_insert_of_mem (mem_kChords.2 ⟨x₀, y₀, hsum, hxy, rfl⟩)
      · refine ⟨(τ y₀, τ x₀), ?_, Or.inr hpx.symm⟩
        rw [hF1]
        exact Finset.mem_insert_of_mem (mem_kChords.2 ⟨y₀, x₀, by omega, by omega, rfl⟩)
  have key : ∃ c₀ : ZMod (n + 1), ∀ A ∈ F1, A.1 + A.2 = c₀ := by
    by_cases hpar : n % 2 = 0
    · -- `n` even: `{0, 0}` is the only degenerate chord
      apply const_sum_of_aligned F1 hnc hdj hT' hcov
      intro A hA B hB hAA hBB
      have hA0 : A = (0, 0) := by
        rw [hF1, Finset.mem_insert] at hA
        rcases hA with h | h
        · exact h
        · exfalso
          obtain ⟨xa, ya, hsa, hlea, hAe⟩ := mem_kChords.mp h
          have hxa : xa = ya := by
            apply τ.injective
            rw [hAe] at hAA
            exact hAA
          have hvva : xa.val = ya.val := by rw [hxa]
          omega
      have hB0 : B = (0, 0) := by
        rw [hF1, Finset.mem_insert] at hB
        rcases hB with h | h
        · exact h
        · exfalso
          obtain ⟨xb, yb, hsb, hleb, hBe⟩ := mem_kChords.mp h
          have hxb : xb = yb := by
            apply τ.injective
            rw [hBe] at hBB
            exact hBB
          have hvvb : xb.val = yb.val := by rw [hxb]
          omega
      rw [hA0, hB0]
    · -- `n` odd: a second degenerate chord `{τ x₀, τ x₀}`, antipodal to `{0, 0}`
      have hnodd : n % 2 = 1 := by omega
      set x₀ := (((n + 1) / 2 : ℕ) : ZMod (n + 1)) with hx₀
      have hx₀v : x₀.val = (n + 1) / 2 := by
        rw [hx₀, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega : (n + 1) / 2 < n + 1)]
      have hdegvals : ∀ A ∈ F1, A.1 = A.2 → A = (0, 0) ∨ A = (τ x₀, τ x₀) := by
        intro A hA hAA
        rw [hF1, Finset.mem_insert] at hA
        rcases hA with h | h
        · exact Or.inl h
        · right
          obtain ⟨xa, ya, hsa, hlea, hAe⟩ := mem_kChords.mp h
          have hxa : xa = ya := by
            apply τ.injective
            rw [hAe] at hAA
            exact hAA
          have hvva : xa.val = ya.val := by rw [hxa]
          have hv : xa.val = (n + 1) / 2 := by omega
          have hxx : xa = x₀ := by
            apply ZMod.val_injective
            rw [hv, hx₀v]
          have hyy : ya = x₀ := by rw [← hxa, hxx]
          rw [hAe, hxx, hyy]
      have hx₀0 : x₀ ≠ 0 := by
        intro he
        have h1 : x₀.val = 0 := by rw [he, ZMod.val_zero]
        omega
      have hq0 : τ x₀ ≠ 0 := by
        intro he
        apply hx₀0
        have h1 : x₀ = 0 := τ.injective (by rw [he, hτ0])
        exact h1
      have hqF : (τ x₀, τ x₀) ∈ F1 := by
        rw [hF1]
        exact Finset.mem_insert_of_mem (mem_kChords.2 ⟨x₀, x₀, by omega, le_refl _, rfl⟩)
      have hanti : τ x₀ + τ x₀ = (0 : ZMod (n + 1)) + 0 :=
        two_degenerate_sum_eq hdj hT' hcov hq0.symm
          (by rw [hF1]; exact Finset.mem_insert_self _ _) hqF hdegvals
      apply const_sum_of_aligned_two F1 hnc hdj hT' hcov
      intro A hA B hB hAA hBB
      rcases hdegvals A hA hAA with hA' | hA' <;> rcases hdegvals B hB hBB with hB' | hB'
      · exact Or.inl (hA'.trans hB'.symm)
      · right
        rw [hA', hB']
        show (0 : ZMod (n + 1)) + 0 = τ x₀ + τ x₀
        exact hanti.symm
      · right
        rw [hA', hB']
        show τ x₀ + τ x₀ = (0 : ZMod (n + 1)) + 0
        exact hanti
      · exact Or.inl (hA'.trans hB'.symm)
  obtain ⟨c₀, hc₀⟩ := key
  have hc₀v : c₀ = 0 := by
    have h := hc₀ (0, 0) (by rw [hF1]; exact Finset.mem_insert_self _ _)
    rw [show ((0 : ZMod (n + 1)), (0 : ZMod (n + 1))).1 + ((0, 0)).2 =
        (0 : ZMod (n + 1)) + 0 from rfl, zero_add] at h
    exact h.symm
  by_cases hx0 : x = 0
  · rw [hx0, neg_zero, hτ0, add_zero]
  · have hxv : 1 ≤ x.val := by
      by_contra h0
      have hz : x.val = 0 := by omega
      apply hx0
      have e := ZMod.natCast_zmod_val x
      rw [hz, Nat.cast_zero] at e
      exact e.symm
    set y := ((n + 1 - x.val : ℕ) : ZMod (n + 1)) with hy
    have hyv : y.val = n + 1 - x.val := by
      rw [hy, ZMod.val_natCast, Nat.mod_eq_of_lt (by have h := ZMod.val_lt x; omega :
        n + 1 - x.val < n + 1)]
    have hsum : x.val + y.val = n + 1 := by have h := ZMod.val_lt x; omega
    have hye : y = -x := by
      have h2 : x + y = (0 : ZMod (n + 1)) := by
        have h3 : x + y = ((x.val + y.val : ℕ) : ZMod (n + 1)) := by
          conv_lhs => rw [← ZMod.natCast_zmod_val x, ← ZMod.natCast_zmod_val y]
          rw [← Nat.cast_add]
        rw [h3, hsum, ZMod.natCast_self]
      rw [eq_neg_iff_add_eq_zero, add_comm y x]
      exact h2
    by_cases hxy : x.val ≤ y.val
    · have hmem : (τ x, τ y) ∈ F1 := by
        rw [hF1]
        exact Finset.mem_insert_of_mem (mem_kChords.2 ⟨x, y, hsum, hxy, rfl⟩)
      have h := hc₀ _ hmem
      rw [show (τ x, τ y).1 + (τ x, τ y).2 = τ x + τ y from rfl, hc₀v, hye] at h
      exact h
    · have hmem : (τ y, τ x) ∈ F1 := by
        rw [hF1]
        exact Finset.mem_insert_of_mem (mem_kChords.2 ⟨y, x, by omega, by omega, rfl⟩)
      have h := hc₀ _ hmem
      rw [show (τ y, τ x).1 + (τ y, τ x).2 = τ y + τ x from rfl, hc₀v, hye,
        add_comm (τ (-x)) (τ x)] at h
      exact h

/-- A Type 2 beautiful labelling is linear: this is the official solution's
description of Type 2 arrangements (the relation `f(-ak) = k`). -/
theorem type2_lin {n : ℕ} (hn : 2 ≤ n) {τ : ZMod (n + 1) ≃ ZMod (n + 1)}
    (hτ : Beautiful τ) (hτ0 : τ 0 = 0) (hT : Type2 τ) : Linear τ :=
  linear_of_two_sums hn hτ0 (fun x => sum_kChords_succ_of_type2 hn hτ hτ0 hT x)
    (fun x => sum_kChords_n hn hτ hτ0 x)

/-! ## Existence of the Type 1 insertion -/

/-- Chord `X` lies strictly inside the value span of chord `Y` (both endpoint
values of `X` are strictly between the two endpoint values of `Y`). -/
def ChordStrictlyInside {N : ℕ} (X Y : Chord N) : Prop :=
  min Y.1.val Y.2.val < X.1.val ∧ X.1.val < max Y.1.val Y.2.val ∧
    min Y.1.val Y.2.val < X.2.val ∧ X.2.val < max Y.1.val Y.2.val

/-- A nonzero element of `ZMod N` has positive value. -/
theorem ExtParallel.val_pos_of_ne_zero {N : ℕ} [NeZero N] {a : ZMod N} (ha : a ≠ 0) :
    1 ≤ a.val := by
  by_contra h0
  have hz : a.val = 0 := by omega
  apply ha
  have e := ZMod.natCast_zmod_val a
  rw [hz, Nat.cast_zero] at e
  exact e.symm

/-- Every nonzero position is covered by some `(n+1)`-chord. -/
theorem ExtParallel.coverAux {n : ℕ} (hn : 2 ≤ n) {τ : ZMod (n + 1) ≃ ZMod (n + 1)}
    (hτ0 : τ 0 = 0) {p : ZMod (n + 1)} (hp : p ≠ 0) :
    ∃ X ∈ kChords τ (n + 1), p = X.1 ∨ p = X.2 := by
  haveI : NeZero (n + 1) := ⟨by omega⟩
  set x₀ := τ.symm p with hx₀
  have hpx : τ x₀ = p := Equiv.apply_symm_apply _ _
  have hx₀0 : x₀ ≠ 0 := by
    intro he
    rw [he, hτ0] at hpx
    exact hp hpx.symm
  have hx₀v : 1 ≤ x₀.val := ExtParallel.val_pos_of_ne_zero hx₀0
  set y₀ := ((n + 1 - x₀.val : ℕ) : ZMod (n + 1)) with hy₀
  have hy₀v : y₀.val = n + 1 - x₀.val := by
    rw [hy₀, ZMod.val_natCast, Nat.mod_eq_of_lt (by have h := ZMod.val_lt x₀; omega :
      n + 1 - x₀.val < n + 1)]
  have hsum : x₀.val + y₀.val = n + 1 := by have h := ZMod.val_lt x₀; omega
  by_cases hxy : x₀.val ≤ y₀.val
  · exact ⟨(τ x₀, τ y₀), mem_kChords.2 ⟨x₀, y₀, hsum, hxy, rfl⟩, Or.inl hpx.symm⟩
  · exact ⟨(τ y₀, τ x₀), mem_kChords.2 ⟨y₀, x₀, by omega, by omega, rfl⟩, Or.inr hpx.symm⟩

/-- Endpoint positions of an `(n+1)`-chord have positive value. -/
theorem ExtParallel.one_le_val {n : ℕ} (hn : 2 ≤ n) {τ : ZMod (n + 1) ≃ ZMod (n + 1)}
    (hτ0 : τ 0 = 0) {X : Chord (n + 1)} (hX : X ∈ kChords τ (n + 1)) :
    1 ≤ X.1.val ∧ 1 ≤ X.2.val := by
  haveI : NeZero (n + 1) := ⟨by omega⟩
  obtain ⟨x, y, hsum, hle, hXe⟩ := mem_kChords.mp hX
  have hx1 : 1 ≤ x.val := by have h := ZMod.val_lt y; omega
  have hy1 : 1 ≤ y.val := by have h := ZMod.val_lt x; omega
  have htx : τ x ≠ 0 := by
    intro he
    have hx0 : x = 0 := τ.injective (by rw [he, hτ0])
    rw [hx0, ZMod.val_zero] at hx1
    omega
  have hty : τ y ≠ 0 := by
    intro he
    have hy0 : y = 0 := τ.injective (by rw [he, hτ0])
    rw [hy0, ZMod.val_zero] at hy1
    omega
  subst hXe
  exact ⟨ExtParallel.val_pos_of_ne_zero htx, ExtParallel.val_pos_of_ne_zero hty⟩

/-- The sides lemma: every `(n+1)`-chord `X ≠ B` has both endpoint values in
`[1, w - 1]` or both in `[w + 1, n - 1]` (a mixed chord would cross `B`). -/
theorem ExtParallel.sidesAux {n : ℕ} (hn : 2 ≤ n) {τ : ZMod (n + 1) ≃ ZMod (n + 1)}
    (hτ : Beautiful τ) (hτ0 : τ 0 = 0) {B : Chord (n + 1)} {w : ℕ}
    (hB : B ∈ kChords τ (n + 1))
    (hBw : (B.1.val = n ∧ B.2.val = w) ∨ (B.1.val = w ∧ B.2.val = n))
    (hw1 : 1 ≤ w) (hwn : w ≤ n)
    {X : Chord (n + 1)} (hX : X ∈ kChords τ (n + 1)) (hXB : X ≠ B) :
    (1 ≤ X.1.val ∧ X.1.val ≤ w - 1 ∧ 1 ≤ X.2.val ∧ X.2.val ≤ w - 1) ∨
      (w + 1 ≤ X.1.val ∧ X.1.val ≤ n - 1 ∧ w + 1 ≤ X.2.val ∧ X.2.val ≤ n - 1) := by
  haveI : NeZero (n + 1) := ⟨by omega⟩
  obtain ⟨g1, g2⟩ := ExtParallel.one_le_val hn hτ0 hX
  have hlt1 := ZMod.val_lt X.1
  have hlt2 := ZMod.val_lt X.2
  have hd := kChords_disjoint X hX B hB hXB
  have hXB1 : X.1.val ≠ B.1.val := fun h => hd.1 (ZMod.val_injective _ h)
  have hXB2 : X.1.val ≠ B.2.val := fun h => hd.2.1 (ZMod.val_injective _ h)
  have hXB3 : X.2.val ≠ B.1.val := fun h => hd.2.2.1 (ZMod.val_injective _ h)
  have hXB4 : X.2.val ≠ B.2.val := fun h => hd.2.2.2 (ZMod.val_injective _ h)
  have hnc := Beautiful.kChords_nonCrossing hτ (n + 1) B hB X hX (Ne.symm hXB)
  rcases hBw with ⟨hb1, hb2⟩ | ⟨hb1, hb2⟩
  · -- `B.1.val = n`, `B.2.val = w`: both betweennesses wrap to below `w`
    have hc : B.2.val ≤ B.1.val := by omega
    have h1 : X.1.val ≤ B.1.val := by omega
    have h2 : X.2.val ≤ B.1.val := by omega
    rw [sbtw_of_val_ge h1 hc, sbtw_of_val_ge h2 hc] at hnc
    omega
  · -- `B.1.val = w`, `B.2.val = n`: both betweennesses are the plain interval `(w, n)`
    have hac : B.1.val ≤ B.2.val := by omega
    rw [sbtw_of_val_le hac, sbtw_of_val_le hac] at hnc
    omega

/-- The nested lemma: two distinct `(n+1)`-chords on the same side of `B` are
strictly nested (otherwise `{B, X, Y}` would not be aligned). -/
theorem ExtParallel.nestAux {n : ℕ} (hn : 2 ≤ n) {τ : ZMod (n + 1) ≃ ZMod (n + 1)}
    (hτ : Beautiful τ) {B : Chord (n + 1)} {w : ℕ}
    (hB : B ∈ kChords τ (n + 1))
    (hBw : (B.1.val = n ∧ B.2.val = w) ∨ (B.1.val = w ∧ B.2.val = n))
    (hw1 : 1 ≤ w) (hwn : w ≤ n)
    {X Y : Chord (n + 1)} (hX : X ∈ kChords τ (n + 1)) (hY : Y ∈ kChords τ (n + 1))
    (hXB : X ≠ B) (hYB : Y ≠ B) (hXY : X ≠ Y)
    (hside : (1 ≤ X.1.val ∧ X.1.val ≤ w - 1 ∧ 1 ≤ X.2.val ∧ X.2.val ≤ w - 1 ∧
        1 ≤ Y.1.val ∧ Y.1.val ≤ w - 1 ∧ 1 ≤ Y.2.val ∧ Y.2.val ≤ w - 1) ∨
      (w + 1 ≤ X.1.val ∧ X.1.val ≤ n - 1 ∧ w + 1 ≤ X.2.val ∧ X.2.val ≤ n - 1 ∧
        w + 1 ≤ Y.1.val ∧ Y.1.val ≤ n - 1 ∧ w + 1 ≤ Y.2.val ∧ Y.2.val ≤ n - 1)) :
    ChordStrictlyInside X Y ∨ ChordStrictlyInside Y X := by
  haveI : NeZero (n + 1) := ⟨by omega⟩
  have hdXB := kChords_disjoint X hX B hB hXB
  have hdYB := kChords_disjoint Y hY B hB hYB
  have hdXY := kChords_disjoint X hX Y hY hXY
  have hXB1 : X.1.val ≠ B.1.val := fun h => hdXB.1 (ZMod.val_injective _ h)
  have hXB2 : X.1.val ≠ B.2.val := fun h => hdXB.2.1 (ZMod.val_injective _ h)
  have hXB3 : X.2.val ≠ B.1.val := fun h => hdXB.2.2.1 (ZMod.val_injective _ h)
  have hXB4 : X.2.val ≠ B.2.val := fun h => hdXB.2.2.2 (ZMod.val_injective _ h)
  have hYB1 : Y.1.val ≠ B.1.val := fun h => hdYB.1 (ZMod.val_injective _ h)
  have hYB2 : Y.1.val ≠ B.2.val := fun h => hdYB.2.1 (ZMod.val_injective _ h)
  have hYB3 : Y.2.val ≠ B.1.val := fun h => hdYB.2.2.1 (ZMod.val_injective _ h)
  have hYB4 : Y.2.val ≠ B.2.val := fun h => hdYB.2.2.2 (ZMod.val_injective _ h)
  have hXY1 : X.1.val ≠ Y.1.val := fun h => hdXY.1 (ZMod.val_injective _ h)
  have hXY2 : X.1.val ≠ Y.2.val := fun h => hdXY.2.1 (ZMod.val_injective _ h)
  have hXY3 : X.2.val ≠ Y.1.val := fun h => hdXY.2.2.1 (ZMod.val_injective _ h)
  have hXY4 : X.2.val ≠ Y.2.val := fun h => hdXY.2.2.2 (ZMod.val_injective _ h)
  have hltX1 := ZMod.val_lt X.1
  have hltX2 := ZMod.val_lt X.2
  have hltY1 := ZMod.val_lt Y.1
  have hltY2 := ZMod.val_lt Y.2
  have hal := aligned_kChords (n + 1) τ hτ (n + 1) B hB X hX Y hY (Ne.symm hXB) hXY
    (Ne.symm hYB)
  rcases hBw with ⟨hb1, hb2⟩ | ⟨hb1, hb2⟩
  · -- `B.1.val = n`, `B.2.val = w`
    have hB2le : B.2.val ≤ B.1.val := by omega
    have hX1le : X.1.val ≤ B.1.val := by omega
    have hX2le : X.2.val ≤ B.1.val := by omega
    have hY1le : Y.1.val ≤ B.1.val := by omega
    have hY2le : Y.2.val ≤ B.1.val := by omega
    have hX1lt : X.1.val < B.1.val := by omega
    have hX2lt : X.2.val < B.1.val := by omega
    have hY1lt : Y.1.val < B.1.val := by omega
    have hY2lt : Y.2.val < B.1.val := by omega
    rcases hal with h | h | h
    · exfalso
      unfold ChordSep at h
      rw [sbtw_of_val_ge hX1le hB2le, sbtw_of_val_ge hX2le hB2le,
        sbtw_of_val_ge hY1le hB2le, sbtw_of_val_ge hY2le hB2le] at h
      rcases hside with hs | hs <;> omega
    · refine Or.inr ?_
      unfold ChordSep at h
      unfold ChordStrictlyInside
      rw [sbtw_of_lt_max hX1lt hX2lt] at h
      rcases hside with hs | hs
      · rw [sbtw_of_lt_max (by omega : X.1.val < B.2.val)
          (by omega : X.2.val < B.2.val)] at h
        by_cases hXe : X.1 = X.2
        · rw [hXe] at h
          simp only [sbtw_zmod_def] at h
          omega
        · have hXne : X.1.val ≠ X.2.val := fun hh => hXe (ZMod.val_injective _ hh)
          rcases le_total X.1.val X.2.val with hX12 | hX12
          · rw [min_eq_left hX12, max_eq_right hX12]
            simp only [sbtw_of_val_le hX12] at h
            omega
          · rw [min_eq_right (by omega : X.2.val ≤ X.1.val),
              max_eq_left (by omega : X.1.val ≥ X.2.val)]
            simp only [sbtw_of_val_gt (by omega : X.2.val < X.1.val)] at h
            omega
      · rw [sbtw_of_gt_min (by omega : B.2.val < X.1.val)
          (by omega : B.2.val < X.2.val)] at h
        by_cases hXe : X.1 = X.2
        · rw [hXe] at h
          simp only [sbtw_zmod_def] at h
          omega
        · have hXne : X.1.val ≠ X.2.val := fun hh => hXe (ZMod.val_injective _ hh)
          rcases le_total X.1.val X.2.val with hX12 | hX12
          · rw [min_eq_left hX12, max_eq_right hX12]
            simp only [sbtw_of_val_le hX12] at h
            omega
          · rw [min_eq_right (by omega : X.2.val ≤ X.1.val),
              max_eq_left (by omega : X.1.val ≥ X.2.val)]
            simp only [sbtw_of_val_gt (by omega : X.2.val < X.1.val)] at h
            omega
    · refine Or.inl ?_
      unfold ChordSep at h
      unfold ChordStrictlyInside
      rw [sbtw_of_lt_max hY1lt hY2lt] at h
      rcases hside with hs | hs
      · rw [sbtw_of_lt_max (by omega : Y.1.val < B.2.val)
          (by omega : Y.2.val < B.2.val)] at h
        by_cases hYe : Y.1 = Y.2
        · rw [hYe] at h
          simp only [sbtw_zmod_def] at h
          omega
        · have hYne : Y.1.val ≠ Y.2.val := fun hh => hYe (ZMod.val_injective _ hh)
          rcases le_total Y.1.val Y.2.val with hY12 | hY12
          · rw [min_eq_left hY12, max_eq_right hY12]
            simp only [sbtw_of_val_le hY12] at h
            omega
          · rw [min_eq_right (by omega : Y.2.val ≤ Y.1.val),
              max_eq_left (by omega : Y.1.val ≥ Y.2.val)]
            simp only [sbtw_of_val_gt (by omega : Y.2.val < Y.1.val)] at h
            omega
      · rw [sbtw_of_gt_min (by omega : B.2.val < Y.1.val)
          (by omega : B.2.val < Y.2.val)] at h
        by_cases hYe : Y.1 = Y.2
        · rw [hYe] at h
          simp only [sbtw_zmod_def] at h
          omega
        · have hYne : Y.1.val ≠ Y.2.val := fun hh => hYe (ZMod.val_injective _ hh)
          rcases le_total Y.1.val Y.2.val with hY12 | hY12
          · rw [min_eq_left hY12, max_eq_right hY12]
            simp only [sbtw_of_val_le hY12] at h
            omega
          · rw [min_eq_right (by omega : Y.2.val ≤ Y.1.val),
              max_eq_left (by omega : Y.1.val ≥ Y.2.val)]
            simp only [sbtw_of_val_gt (by omega : Y.2.val < Y.1.val)] at h
            omega
  · -- `B.1.val = w`, `B.2.val = n`
    have hB1le : B.1.val ≤ B.2.val := by omega
    have hX1lt2 : X.1.val < B.2.val := by omega
    have hX2lt2 : X.2.val < B.2.val := by omega
    have hY1lt2 : Y.1.val < B.2.val := by omega
    have hY2lt2 : Y.2.val < B.2.val := by omega
    rcases hal with h | h | h
    · exfalso
      unfold ChordSep at h
      simp only [sbtw_of_val_le hB1le] at h
      rcases hside with hs | hs <;> omega
    · refine Or.inr ?_
      unfold ChordSep at h
      unfold ChordStrictlyInside
      rw [sbtw_of_lt_max hX1lt2 hX2lt2] at h
      rcases hside with hs | hs
      · rw [sbtw_of_lt_max (by omega : X.1.val < B.1.val)
          (by omega : X.2.val < B.1.val)] at h
        by_cases hXe : X.1 = X.2
        · rw [hXe] at h
          simp only [sbtw_zmod_def] at h
          omega
        · have hXne : X.1.val ≠ X.2.val := fun hh => hXe (ZMod.val_injective _ hh)
          rcases le_total X.1.val X.2.val with hX12 | hX12
          · rw [min_eq_left hX12, max_eq_right hX12]
            simp only [sbtw_of_val_le hX12] at h
            omega
          · rw [min_eq_right (by omega : X.2.val ≤ X.1.val),
              max_eq_left (by omega : X.1.val ≥ X.2.val)]
            simp only [sbtw_of_val_gt (by omega : X.2.val < X.1.val)] at h
            omega
      · rw [sbtw_of_gt_min (by omega : B.1.val < X.1.val)
          (by omega : B.1.val < X.2.val)] at h
        by_cases hXe : X.1 = X.2
        · rw [hXe] at h
          simp only [sbtw_zmod_def] at h
          omega
        · have hXne : X.1.val ≠ X.2.val := fun hh => hXe (ZMod.val_injective _ hh)
          rcases le_total X.1.val X.2.val with hX12 | hX12
          · rw [min_eq_left hX12, max_eq_right hX12]
            simp only [sbtw_of_val_le hX12] at h
            omega
          · rw [min_eq_right (by omega : X.2.val ≤ X.1.val),
              max_eq_left (by omega : X.1.val ≥ X.2.val)]
            simp only [sbtw_of_val_gt (by omega : X.2.val < X.1.val)] at h
            omega
    · refine Or.inl ?_
      unfold ChordSep at h
      unfold ChordStrictlyInside
      rw [sbtw_of_lt_max hY1lt2 hY2lt2] at h
      rcases hside with hs | hs
      · rw [sbtw_of_lt_max (by omega : Y.1.val < B.1.val)
          (by omega : Y.2.val < B.1.val)] at h
        by_cases hYe : Y.1 = Y.2
        · rw [hYe] at h
          simp only [sbtw_zmod_def] at h
          omega
        · have hYne : Y.1.val ≠ Y.2.val := fun hh => hYe (ZMod.val_injective _ hh)
          rcases le_total Y.1.val Y.2.val with hY12 | hY12
          · rw [min_eq_left hY12, max_eq_right hY12]
            simp only [sbtw_of_val_le hY12] at h
            omega
          · rw [min_eq_right (by omega : Y.2.val ≤ Y.1.val),
              max_eq_left (by omega : Y.1.val ≥ Y.2.val)]
            simp only [sbtw_of_val_gt (by omega : Y.2.val < Y.1.val)] at h
            omega
      · rw [sbtw_of_gt_min (by omega : B.1.val < Y.1.val)
          (by omega : B.1.val < Y.2.val)] at h
        by_cases hYe : Y.1 = Y.2
        · rw [hYe] at h
          simp only [sbtw_zmod_def] at h
          omega
        · have hYne : Y.1.val ≠ Y.2.val := fun hh => hYe (ZMod.val_injective _ hh)
          rcases le_total Y.1.val Y.2.val with hY12 | hY12
          · rw [min_eq_left hY12, max_eq_right hY12]
            simp only [sbtw_of_val_le hY12] at h
            omega
          · rw [min_eq_right (by omega : Y.2.val ≤ Y.1.val),
              max_eq_left (by omega : Y.1.val ≥ Y.2.val)]
            simp only [sbtw_of_val_gt (by omega : Y.2.val < Y.1.val)] at h
            omega

/-- The rainbow (tower) lemma: a pairwise strictly nested family of chords covering
a whole value interval `[a, b]`, with all endpoint values in `[a, b]`, is the
rainbow — every chord has endpoint-value sum `a + b`. Proved by induction on the
interval length, peeling off the outermost chord (the chord through `a`, which
nestedness forces to be `{a, b}`). -/
theorem rainbow_of_tower {m : ℕ} [NeZero (m + 1)] :
    ∀ L : ℕ, ∀ (F : Finset (Chord (m + 1))) (a b : ℕ), b - a < L → b < m + 1 →
      ChordDisjoint F →
      (∀ q : ℕ, a ≤ q → q ≤ b → ∃ X ∈ F, X.1.val = q ∨ X.2.val = q) →
      (∀ X ∈ F, a ≤ X.1.val ∧ X.1.val ≤ b ∧ a ≤ X.2.val ∧ X.2.val ≤ b) →
      (∀ X ∈ F, ∀ Y ∈ F, X ≠ Y → ChordStrictlyInside X Y ∨ ChordStrictlyInside Y X) →
      ∀ X ∈ F, X.1.val + X.2.val = a + b := by
  intro L
  induction L with
  | zero =>
    intro F a b hL
    exfalso
    omega
  | succ L IH =>
    intro F a b hL hbN hdj hcov hside hnst X hX
    have cov_unique : ∀ Y₁ ∈ F, ∀ Y₂ ∈ F, ∀ q : ℕ, q < m + 1 →
        (Y₁.1.val = q ∨ Y₁.2.val = q) → (Y₂.1.val = q ∨ Y₂.2.val = q) → Y₁ = Y₂ := by
      intro Y₁ hY₁ Y₂ hY₂ q hqN hq1 hq2
      have hv : (((q : ℕ) : ZMod (m + 1))).val = q := ZMod.val_cast_of_lt hqN
      apply eq_of_shared_endpoint hdj hY₁ hY₂ (p := ((q : ℕ) : ZMod (m + 1)))
      · rcases hq1 with h | h
        · exact Or.inl (ZMod.val_injective _ (by rw [hv, h]))
        · exact Or.inr (ZMod.val_injective _ (by rw [hv, h]))
      · rcases hq2 with h | h
        · exact Or.inl (ZMod.val_injective _ (by rw [hv, h]))
        · exact Or.inr (ZMod.val_injective _ (by rw [hv, h]))
    by_cases hab : b < a
    · obtain ⟨h1, h2, h3, h4⟩ := hside X hX
      omega
    · push Not at hab
      have outer : ∀ Z ∈ F, (Z.1.val = a ∨ Z.2.val = a) → Z.1.val + Z.2.val = a + b := by
        intro Z hZ hZa
        obtain ⟨h1, h2, h3, h4⟩ := hside Z hZ
        have hzmin : min Z.1.val Z.2.val = a := by rcases hZa with h | h <;> omega
        by_contra hsum
        have hzb : max Z.1.val Z.2.val < b := by rcases hZa with h | h <;> omega
        obtain ⟨Y, hY, hYv⟩ := hcov (max Z.1.val Z.2.val + 1) (by omega) (by omega)
        have hYne : Y ≠ Z := by
          intro he
          subst he
          rcases hYv with h' | h' <;> omega
        have hn := hnst Z hZ Y hY (Ne.symm hYne)
        obtain ⟨g1, g2, g3, g4⟩ := hside Y hY
        rcases hn with hn | hn <;> unfold ChordStrictlyInside at hn <;>
          rcases hYv with h' | h' <;> rcases hZa with h'' | h'' <;> omega
      obtain ⟨Z, hZ, hZa⟩ := hcov a (le_refl a) hab
      by_cases hXZ : X = Z
      · rw [hXZ]
        exact outer Z hZ hZa
      · have hZsum := outer Z hZ hZa
        have hZb : Z.1.val = b ∨ Z.2.val = b := by
          obtain ⟨h1, h2, h3, h4⟩ := hside Z hZ
          rcases hZa with h | h <;> omega
        have haN : a < m + 1 := by omega
        obtain ⟨g1, g2, g3, g4⟩ := hside X hX
        have hXa1 : X.1.val ≠ a := fun h => hXZ (cov_unique X hX Z hZ a haN (Or.inl h) hZa)
        have hXa2 : X.2.val ≠ a := fun h => hXZ (cov_unique X hX Z hZ a haN (Or.inr h) hZa)
        have hXb1 : X.1.val ≠ b := fun h => hXZ (cov_unique X hX Z hZ b hbN (Or.inl h) hZb)
        have hXb2 : X.2.val ≠ b := fun h => hXZ (cov_unique X hX Z hZ b hbN (Or.inr h) hZb)
        by_cases hab2 : b ≤ a + 1
        · omega
        · push Not at hab2
          have hdj' : ChordDisjoint (F.erase Z) := fun A hA B' hB' hne =>
            hdj A (Finset.mem_of_mem_erase hA) B' (Finset.mem_of_mem_erase hB') hne
          have hcov' : ∀ q : ℕ, a + 1 ≤ q → q ≤ b - 1 →
              ∃ W ∈ F.erase Z, W.1.val = q ∨ W.2.val = q := by
            intro q hq1 hq2
            obtain ⟨W, hW, hWq⟩ := hcov q (by omega) (by omega)
            have hWne : W ≠ Z := by
              intro he
              subst he
              rcases hWq with h | h <;> rcases hZa with h' | h' <;>
                rcases hZb with h'' | h'' <;> omega
            exact ⟨W, Finset.mem_erase.2 ⟨hWne, hW⟩, hWq⟩
          have hside' : ∀ W ∈ F.erase Z,
              a + 1 ≤ W.1.val ∧ W.1.val ≤ b - 1 ∧ a + 1 ≤ W.2.val ∧ W.2.val ≤ b - 1 := by
            intro W hW
            rw [Finset.mem_erase] at hW
            obtain ⟨hWne, hWF⟩ := hW
            obtain ⟨h1, h2, h3, h4⟩ := hside W hWF
            have hWa1 : W.1.val ≠ a := fun h =>
              hWne (cov_unique W hWF Z hZ a haN (Or.inl h) hZa)
            have hWa2 : W.2.val ≠ a := fun h =>
              hWne (cov_unique W hWF Z hZ a haN (Or.inr h) hZa)
            have hWb1 : W.1.val ≠ b := fun h =>
              hWne (cov_unique W hWF Z hZ b hbN (Or.inl h) hZb)
            have hWb2 : W.2.val ≠ b := fun h =>
              hWne (cov_unique W hWF Z hZ b hbN (Or.inr h) hZb)
            omega
          have hnst' : ∀ A ∈ F.erase Z, ∀ B' ∈ F.erase Z, A ≠ B' →
              ChordStrictlyInside A B' ∨ ChordStrictlyInside B' A :=
            fun A hA B' hB' hne =>
              hnst A (Finset.mem_of_mem_erase hA) B' (Finset.mem_of_mem_erase hB') hne
          have hXe : X ∈ F.erase Z := Finset.mem_erase.2 ⟨hXZ, hX⟩
          have hrec := IH (F.erase Z) (a + 1) (b - 1) (by omega) (by omega) hdj' hcov'
            hside' hnst' X hXe
          omega

/-- The two-sum structure of the `(n+1)`-chords of a normalized beautiful labelling:
with `w` the position value of the partner of position `n` in its chord `B`, every
`(n+1)`-chord has endpoint-value sum `w` (the side of `B` towards position `1`) or
`n + w` (the other side, and `B` itself). -/
theorem ExtParallel.two_sums {n : ℕ} (hn : 2 ≤ n) {τ : ZMod (n + 1) ≃ ZMod (n + 1)}
    (hτ : Beautiful τ) (hτ0 : τ 0 = 0) :
    ∃ w : ℕ, 1 ≤ w ∧ w ≤ n ∧ ∀ A ∈ kChords τ (n + 1),
      A.1.val + A.2.val = w ∨ A.1.val + A.2.val = n + w := by
  haveI : NeZero (n + 1) := ⟨by omega⟩
  set xn := τ.symm ((n : ℕ) : ZMod (n + 1)) with hxn
  have htxn : τ xn = ((n : ℕ) : ZMod (n + 1)) := Equiv.apply_symm_apply _ _
  have hnv : (((n : ℕ) : ZMod (n + 1))).val = n := ZMod.val_cast_of_lt (Nat.lt_succ_self n)
  have hxn0 : xn ≠ 0 := by
    intro he
    have e : (((n : ℕ) : ZMod (n + 1))) = 0 := by rw [← htxn, he, hτ0]
    have h := congrArg ZMod.val e
    rw [hnv, ZMod.val_zero] at h
    omega
  have hxnv : 1 ≤ xn.val := ExtParallel.val_pos_of_ne_zero hxn0
  have hxnN : xn.val ≤ n := by have h := ZMod.val_lt xn; omega
  set yn := ((n + 1 - xn.val : ℕ) : ZMod (n + 1)) with hyn
  have hynv : yn.val = n + 1 - xn.val := by
    rw [hyn, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega : n + 1 - xn.val < n + 1)]
  have hsumn : xn.val + yn.val = n + 1 := by omega
  have hyn0 : yn ≠ 0 := by
    intro he
    have h : yn.val = 0 := by rw [he, ZMod.val_zero]
    omega
  set w := (τ yn).val with hw
  have htxnv : (τ xn).val = n := by rw [htxn, hnv]
  have hw1 : 1 ≤ w := by
    have h0 : τ yn ≠ 0 := by
      intro he
      apply hyn0
      exact τ.injective (by rw [he, hτ0])
    exact ExtParallel.val_pos_of_ne_zero h0
  have hwN : w ≤ n := by have h := ZMod.val_lt (τ yn); omega
  set B : Chord (n + 1) := if xn.val ≤ yn.val then (τ xn, τ yn) else (τ yn, τ xn) with hBdef
  have hB : B ∈ kChords τ (n + 1) := by
    rw [hBdef]
    by_cases hord : xn.val ≤ yn.val
    · rw [if_pos hord]
      exact mem_kChords.2 ⟨xn, yn, hsumn, hord, rfl⟩
    · rw [if_neg hord]
      exact mem_kChords.2 ⟨yn, xn, by omega, by omega, rfl⟩
  have hBw : (B.1.val = n ∧ B.2.val = w) ∨ (B.1.val = w ∧ B.2.val = n) := by
    rw [hBdef]
    by_cases hord : xn.val ≤ yn.val
    · rw [if_pos hord]
      exact Or.inl ⟨htxnv, hw.symm⟩
    · rw [if_neg hord]
      exact Or.inr ⟨hw.symm, htxnv⟩
  refine ⟨w, hw1, hwN, ?_⟩
  have hsum1 : ∀ X ∈ (kChords τ (n + 1)).filter
      (fun X => 1 ≤ X.1.val ∧ X.1.val ≤ w - 1 ∧ 1 ≤ X.2.val ∧ X.2.val ≤ w - 1),
      X.1.val + X.2.val = 1 + (w - 1) := by
    apply rainbow_of_tower ((w - 1) - 1 + 1) _ 1 (w - 1) (by omega) (by omega)
    · intro A hA B' hB' hne
      rw [Finset.mem_filter] at hA hB'
      exact kChords_disjoint A hA.1 B' hB'.1 hne
    · intro q hq1 hq2
      have hqN : q < n + 1 := by omega
      have hq0 : ((q : ℕ) : ZMod (n + 1)) ≠ 0 := by
        intro he
        have h := congrArg ZMod.val he
        rw [ZMod.val_natCast, Nat.mod_eq_of_lt hqN, ZMod.val_zero] at h
        omega
      obtain ⟨X, hX, hpX⟩ := ExtParallel.coverAux hn hτ0 hq0
      have hpXv : X.1.val = q ∨ X.2.val = q := by
        rcases hpX with h | h
        · exact Or.inl (by rw [← h, ZMod.val_natCast, Nat.mod_eq_of_lt hqN])
        · exact Or.inr (by rw [← h, ZMod.val_natCast, Nat.mod_eq_of_lt hqN])
      have hXB : X ≠ B := by
        intro he
        subst he
        rcases hpXv with h | h <;> rcases hBw with ⟨hb1, hb2⟩ | ⟨hb1, hb2⟩ <;> omega
      have hs := ExtParallel.sidesAux hn hτ hτ0 hB hBw hw1 hwN hX hXB
      refine ⟨X, Finset.mem_filter.2 ⟨hX, ?_⟩, hpXv⟩
      rcases hs with hs | hs
      · exact hs
      · rcases hpXv with h | h <;> omega
    · intro X hX
      rw [Finset.mem_filter] at hX
      exact hX.2
    · intro X hX Y hY hXY
      rw [Finset.mem_filter] at hX hY
      have hXB : X ≠ B := by
        intro he
        subst he
        obtain ⟨t1, t2, t3, t4⟩ := hX.2
        rcases hBw with ⟨hb1, hb2⟩ | ⟨hb1, hb2⟩ <;> omega
      have hYB : Y ≠ B := by
        intro he
        subst he
        obtain ⟨t1, t2, t3, t4⟩ := hY.2
        rcases hBw with ⟨hb1, hb2⟩ | ⟨hb1, hb2⟩ <;> omega
      exact ExtParallel.nestAux hn hτ hB hBw hw1 hwN hX.1 hY.1 hXB hYB hXY
        (Or.inl ⟨hX.2.1, hX.2.2.1, hX.2.2.2.1, hX.2.2.2.2, hY.2.1, hY.2.2.1, hY.2.2.2.1,
          hY.2.2.2.2⟩)
  have hsum2 : ∀ X ∈ (kChords τ (n + 1)).filter
      (fun X => w + 1 ≤ X.1.val ∧ X.1.val ≤ n - 1 ∧ w + 1 ≤ X.2.val ∧ X.2.val ≤ n - 1),
      X.1.val + X.2.val = (w + 1) + (n - 1) := by
    apply rainbow_of_tower ((n - 1) - (w + 1) + 1) _ (w + 1) (n - 1) (by omega) (by omega)
    · intro A hA B' hB' hne
      rw [Finset.mem_filter] at hA hB'
      exact kChords_disjoint A hA.1 B' hB'.1 hne
    · intro q hq1 hq2
      have hqN : q < n + 1 := by omega
      have hq0 : ((q : ℕ) : ZMod (n + 1)) ≠ 0 := by
        intro he
        have h := congrArg ZMod.val he
        rw [ZMod.val_natCast, Nat.mod_eq_of_lt hqN, ZMod.val_zero] at h
        omega
      obtain ⟨X, hX, hpX⟩ := ExtParallel.coverAux hn hτ0 hq0
      have hpXv : X.1.val = q ∨ X.2.val = q := by
        rcases hpX with h | h
        · exact Or.inl (by rw [← h, ZMod.val_natCast, Nat.mod_eq_of_lt hqN])
        · exact Or.inr (by rw [← h, ZMod.val_natCast, Nat.mod_eq_of_lt hqN])
      have hXB : X ≠ B := by
        intro he
        subst he
        rcases hpXv with h | h <;> rcases hBw with ⟨hb1, hb2⟩ | ⟨hb1, hb2⟩ <;> omega
      have hs := ExtParallel.sidesAux hn hτ hτ0 hB hBw hw1 hwN hX hXB
      refine ⟨X, Finset.mem_filter.2 ⟨hX, ?_⟩, hpXv⟩
      rcases hs with hs | hs
      · rcases hpXv with h | h <;> omega
      · exact hs
    · intro X hX
      rw [Finset.mem_filter] at hX
      exact hX.2
    · intro X hX Y hY hXY
      rw [Finset.mem_filter] at hX hY
      have hXB : X ≠ B := by
        intro he
        subst he
        obtain ⟨t1, t2, t3, t4⟩ := hX.2
        rcases hBw with ⟨hb1, hb2⟩ | ⟨hb1, hb2⟩ <;> omega
      have hYB : Y ≠ B := by
        intro he
        subst he
        obtain ⟨t1, t2, t3, t4⟩ := hY.2
        rcases hBw with ⟨hb1, hb2⟩ | ⟨hb1, hb2⟩ <;> omega
      exact ExtParallel.nestAux hn hτ hB hBw hw1 hwN hX.1 hY.1 hXB hYB hXY
        (Or.inr ⟨hX.2.1, hX.2.2.1, hX.2.2.2.1, hX.2.2.2.2, hY.2.1, hY.2.2.1, hY.2.2.2.1,
          hY.2.2.2.2⟩)
  intro A hA
  by_cases hAB : A = B
  · subst hAB
    right
    rcases hBw with ⟨hb1, hb2⟩ | ⟨hb1, hb2⟩ <;> omega
  · have hs := ExtParallel.sidesAux hn hτ hτ0 hB hBw hw1 hwN hA hAB
    rcases hs with hs | hs
    · left
      have hAF : A ∈ (kChords τ (n + 1)).filter
          (fun X => 1 ≤ X.1.val ∧ X.1.val ≤ w - 1 ∧ 1 ≤ X.2.val ∧ X.2.val ≤ w - 1) :=
        Finset.mem_filter.2 ⟨hA, hs⟩
      have h := hsum1 A hAF
      omega
    · right
      have hAF : A ∈ (kChords τ (n + 1)).filter
          (fun X => w + 1 ≤ X.1.val ∧ X.1.val ≤ n - 1 ∧ w + 1 ≤ X.2.val ∧ X.2.val ≤ n - 1) :=
        Finset.mem_filter.2 ⟨hA, hs⟩
      have h := hsum2 A hAF
      omega

/-- Existence of the Type 1 insertion: for every normalized beautiful labelling `τ`
there is an insertion parameter `c` making the `(n+1)`-chords of the inserted
arrangement parallel (constant endpoint-sum equal to the new label's position). -/
theorem ExtParallel.exists {n : ℕ} (hn : 2 ≤ n) {τ : ZMod (n + 1) ≃ ZMod (n + 1)}
    (hτ : Beautiful τ) (hτ0 : τ 0 = 0) :
    ∃ c : ZMod (n + 1), ExtParallel τ c := by
  haveI : NeZero (n + 1) := ⟨by omega⟩
  haveI : NeZero (n + 2) := ⟨by omega⟩
  obtain ⟨w, hw1, hwN, h2sum⟩ := ExtParallel.two_sums hn hτ hτ0
  refine ⟨((n + 1 - w : ℕ) : ZMod (n + 1)), ?_⟩
  set c₀ : ZMod (n + 1) := ((n + 1 - w : ℕ) : ZMod (n + 1)) with hc₀
  have hc₀v : c₀.val = n + 1 - w := by
    rw [hc₀, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega : n + 1 - w < n + 1)]
  have hq0 : (rot c₀ τ) 0 = c₀ := by rw [rot_apply, hτ0, zero_add]
  have hqt : (InsertNorm τ c₀) topLabel =
      (((n + 1) - ((rot c₀ τ) 0).val : ℕ) : ZMod (n + 2)) := Insert_top (rot c₀ τ) _
  intro A hA
  obtain ⟨x, y, hsum, hle, hAe⟩ := mem_kChords.mp hA
  rw [hAe]
  show (InsertNorm τ c₀) x + (InsertNorm τ c₀) y = (InsertNorm τ c₀) topLabel
  rw [hqt, hq0, hc₀v, show (n + 1) - (n + 1 - w) = w from by omega]
  by_cases hx0 : x = 0
  · subst hx0
    have hyv : y.val = n + 1 := by rw [ZMod.val_zero] at hsum; omega
    have hyt : y = topLabel := ZMod.val_injective _ (by rw [hyv, topLabel_val])
    rw [hyt, InsertNorm_zero, zero_add, hqt, hq0, hc₀v,
      show (n + 1) - (n + 1 - w) = w from by omega]
  · have hxv1 : 1 ≤ x.val := ExtParallel.val_pos_of_ne_zero hx0
    have hyv2 : y.val ≤ n := by have h := ZMod.val_lt x; omega
    have hxv2 : x.val ≤ n := by omega
    set x' := ((x.val : ℕ) : ZMod (n + 1)) with hx'
    set y' := ((y.val : ℕ) : ZMod (n + 1)) with hy'
    have hx'v : x'.val = x.val := by
      rw [hx', ZMod.val_natCast, Nat.mod_eq_of_lt (by omega : x.val < n + 1)]
    have hy'v : y'.val = y.val := by
      rw [hy', ZMod.val_natCast, Nat.mod_eq_of_lt (by omega : y.val < n + 1)]
    have hxe : x = ((x'.val : ℕ) : ZMod (n + 2)) := by
      rw [hx'v, ZMod.natCast_zmod_val]
    have hye : y = ((y'.val : ℕ) : ZMod (n + 2)) := by
      rw [hy'v, ZMod.natCast_zmod_val]
    have hsum' : x'.val + y'.val = n + 1 := by omega
    have hle' : x'.val ≤ y'.val := by omega
    have hmem : (τ x', τ y') ∈ kChords τ (n + 1) :=
      mem_kChords.2 ⟨x', y', hsum', hle', rfl⟩
    have hu1 : 1 ≤ (τ x').val := by
      apply ExtParallel.val_pos_of_ne_zero
      intro he
      have hx'0 : x' = 0 := τ.injective (by rw [he, hτ0])
      rw [hx'0, ZMod.val_zero] at hx'v
      omega
    have hv1 : 1 ≤ (τ y').val := by
      apply ExtParallel.val_pos_of_ne_zero
      intro he
      have hy'0 : y' = 0 := τ.injective (by rw [he, hτ0])
      rw [hy'0, ZMod.val_zero] at hy'v
      omega
    have hult := ZMod.val_lt (τ x')
    have hvlt := ZMod.val_lt (τ y')
    have hu : (τ x' + c₀).val =
        if (τ x').val < w then (τ x').val + (n + 1 - w) else (τ x').val - w := by
      have hadd : (τ x' + c₀ : ZMod (n + 1)) =
          (((τ x').val + (n + 1 - w) : ℕ) : ZMod (n + 1)) := by
        conv_lhs => rw [← ZMod.natCast_zmod_val (τ x')]
        rw [hc₀, ← Nat.cast_add]
      rw [hadd, ZMod.val_natCast]
      by_cases h1 : (τ x').val < w
      · rw [if_pos h1, Nat.mod_eq_of_lt (by omega : (τ x').val + (n + 1 - w) < n + 1)]
      · rw [if_neg h1,
          show (τ x').val + (n + 1 - w) = ((τ x').val - w) + (n + 1) from by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : (τ x').val - w < n + 1)]
    have hv : (τ y' + c₀).val =
        if (τ y').val < w then (τ y').val + (n + 1 - w) else (τ y').val - w := by
      have hadd : (τ y' + c₀ : ZMod (n + 1)) =
          (((τ y').val + (n + 1 - w) : ℕ) : ZMod (n + 1)) := by
        conv_lhs => rw [← ZMod.natCast_zmod_val (τ y')]
        rw [hc₀, ← Nat.cast_add]
      rw [hadd, ZMod.val_natCast]
      by_cases h2 : (τ y').val < w
      · rw [if_pos h2, Nat.mod_eq_of_lt (by omega : (τ y').val + (n + 1 - w) < n + 1)]
      · rw [if_neg h2,
          show (τ y').val + (n + 1 - w) = ((τ y').val - w) + (n + 1) from by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : (τ y').val - w < n + 1)]
    have hfin : ((((w + 1 + (τ x' + c₀).val) + (w + 1 + (τ y' + c₀).val) : ℕ)) :
        ZMod (n + 2)) = ((w : ℕ) : ZMod (n + 2)) := by
      apply ZMod.val_injective (n + 2)
      rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega : w < n + 2)]
      rcases (show (τ x').val + (τ y').val = w ∨ (τ x').val + (τ y').val = n + w from
          h2sum _ hmem) with hs | hs
      · have h1 : (τ x').val < w := by omega
        have h2 : (τ y').val < w := by omega
        rw [hu, hv, if_pos h1, if_pos h2,
          show (w + 1 + ((τ x').val + (n + 1 - w))) + (w + 1 + ((τ y').val + (n + 1 - w))) =
            w + 2 * (n + 2) from by omega,
          Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega : w < n + 2)]
      · have h1 : ¬ (τ x').val < w := by omega
        have h2 : ¬ (τ y').val < w := by omega
        rw [hu, hv, if_neg h1, if_neg h2,
          show (w + 1 + ((τ x').val - w)) + (w + 1 + ((τ y').val - w)) =
            w + (n + 2) from by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : w < n + 2)]
    have e1 : (((w : ℕ) : ZMod (n + 2)) + 1 + (((τ x' + c₀).val : ℕ) : ZMod (n + 2))) =
        (((w + 1 + (τ x' + c₀).val : ℕ)) : ZMod (n + 2)) := by
      conv_lhs => rw [← Nat.cast_one, ← Nat.cast_add, ← Nat.cast_add]
    have e2 : (((w : ℕ) : ZMod (n + 2)) + 1 + (((τ y' + c₀).val : ℕ) : ZMod (n + 2))) =
        (((w + 1 + (τ y' + c₀).val : ℕ)) : ZMod (n + 2)) := by
      conv_lhs => rw [← Nat.cast_one, ← Nat.cast_add, ← Nat.cast_add]
    rw [hxe, hye, InsertNorm_apply, InsertNorm_apply, hq0, hc₀v,
      show (n + 1) - (n + 1 - w) = w from by omega, e1, e2, ← Nat.cast_add]
    exact hfin

/-- The `(n+1)`-chords together with `{0, 0}` are non-crossing (for a beautiful
labelling). -/
theorem chordNonCrossing_insert_zero {n : ℕ} {τ : ZMod (n + 1) ≃ ZMod (n + 1)}
    (hτ : Beautiful τ) : ChordNonCrossing (insert (0, 0) (kChords τ (n + 1))) := by
  intro A hA B hB hne
  rw [Finset.mem_insert] at hA hB
  rcases hA with rfl | hA
  · exact ⟨fun h => absurd h sbtw_irrefl_left_right,
      fun h => absurd h sbtw_irrefl_left_right⟩
  · rcases hB with rfl | hB
    · exact Iff.rfl
    · exact Beautiful.kChords_nonCrossing hτ (n + 1) A hA B hB hne

/-- The `(n+1)`-chords together with `{0, 0}` are vertex-disjoint (when `τ 0 = 0`). -/
theorem chordDisjoint_insert_zero {n : ℕ} {τ : ZMod (n + 1) ≃ ZMod (n + 1)}
    (hτ0 : τ 0 = 0) : ChordDisjoint (insert (0, 0) (kChords τ (n + 1))) := by
  intro A hA B hB hne
  rw [Finset.mem_insert] at hA hB
  rcases hA with rfl | hA
  · rcases hB with rfl | hB
    · exact absurd rfl hne
    · obtain ⟨u, v, hsumu, hleu, hBe⟩ := mem_kChords.mp hB
      rw [hBe]
      have huv : u ≠ 0 := by
        intro he
        have h1 : u.val = 0 := by rw [he, ZMod.val_zero]
        have h2 := ZMod.val_lt v
        omega
      have hvv : v ≠ 0 := by
        intro he
        have h1 : v.val = 0 := by rw [he, ZMod.val_zero]
        have h2 := ZMod.val_lt u
        omega
      have hu0 : τ u ≠ 0 := by
        intro he
        apply huv
        have h3 : u = 0 := τ.injective (by rw [he, hτ0])
        exact h3
      have hv0 : τ v ≠ 0 := by
        intro he
        apply hvv
        have h3 : v = 0 := τ.injective (by rw [he, hτ0])
        exact h3
      exact ⟨fun h => hu0 h.symm, fun h => hv0 h.symm,
        fun h => hu0 h.symm, fun h => hv0 h.symm⟩
  · rcases hB with rfl | hB
    · obtain ⟨u, v, hsumu, hleu, hAe⟩ := mem_kChords.mp hA
      rw [hAe]
      have huv : u ≠ 0 := by
        intro he
        have h1 : u.val = 0 := by rw [he, ZMod.val_zero]
        have h2 := ZMod.val_lt v
        omega
      have hvv : v ≠ 0 := by
        intro he
        have h1 : v.val = 0 := by rw [he, ZMod.val_zero]
        have h2 := ZMod.val_lt u
        omega
      have hu0 : τ u ≠ 0 := by
        intro he
        apply huv
        have h3 : u = 0 := τ.injective (by rw [he, hτ0])
        exact h3
      have hv0 : τ v ≠ 0 := by
        intro he
        apply hvv
        have h3 : v = 0 := τ.injective (by rw [he, hτ0])
        exact h3
      exact ⟨hu0, hu0, fun h => hv0 h, fun h => hv0 h⟩
    · exact kChords_disjoint A hA B hB hne

/-- If `0` is a valid insertion parameter, the labelling is of Type 2: every
`(n+1)`-chord has endpoint sum `0` (the "first parallel family"), so `{0, 0}`
is aligned with the chords. -/
theorem type2_of_extParallel_zero {n : ℕ} (hn : 2 ≤ n) {τ : ZMod (n + 1) ≃ ZMod (n + 1)}
    (hτ : Beautiful τ) (hτ0 : τ 0 = 0) (h : ExtParallel τ 0) : Type2 τ := by
  haveI : NeZero (n + 1) := ⟨by omega⟩
  have hsum : ∀ A ∈ insert (0, 0) (kChords τ (n + 1)), A.1 + A.2 = 0 := by
    intro A hA
    rw [Finset.mem_insert] at hA
    rcases hA with rfl | hA
    · show (0 : ZMod (n + 1)) + 0 = 0
      rw [add_zero]
    · obtain ⟨x, y, hs, hle, hAe⟩ := mem_kChords.mp hA
      have hx0 : x ≠ 0 := by
        intro he
        have h1 : x.val = 0 := by rw [he, ZMod.val_zero]
        have h2 := ZMod.val_lt y
        omega
      have hxv : 1 ≤ x.val := by
        by_contra h0
        have hz : x.val = 0 := by omega
        apply hx0
        have e := ZMod.natCast_zmod_val x
        rw [hz, Nat.cast_zero] at e
        exact e.symm
      have hstar := ExtParallel.star hτ0 h hx0
      rw [add_zero, add_zero, ZMod.val_zero, zero_add] at hstar
      have hyv : y = (((n + 1) - x.val : ℕ) : ZMod (n + 1)) := by
        apply ZMod.val_injective (n + 1)
        rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by have h2 := ZMod.val_lt x; omega :
          (n + 1) - x.val < n + 1)]
        have h2 := ZMod.val_lt y
        omega
      rw [← hyv] at hstar
      rcases hstar with hstar | ⟨hle1, -⟩
      · have h2 : τ x + τ y = (((τ x).val + (τ y).val : ℕ) : ZMod (n + 1)) := by
          conv_lhs => rw [← ZMod.natCast_zmod_val (τ x), ← ZMod.natCast_zmod_val (τ y)]
          rw [← Nat.cast_add]
        rw [hAe]
        show (τ x + τ y : ZMod (n + 1)) = 0
        rw [h2, hstar, ZMod.natCast_self]
      · omega
  show ChordAligned (insert (0, 0) (kChords τ (n + 1)))
  exact ChordAligned_of_const_sum (chordNonCrossing_insert_zero hτ)
    (chordDisjoint_insert_zero hτ0) hsum

/-- The value of a nonzero valid insertion parameter is forced: `c.val = n + 1 - w`,
where `w` is the position of the partner of the label sitting at position `n`. -/
theorem val_eq_of_extParallel_ne_zero {n : ℕ} (hn : 2 ≤ n) {τ : ZMod (n + 1) ≃ ZMod (n + 1)}
    (hτ0 : τ 0 = 0) {c : ZMod (n + 1)} (h : ExtParallel τ c) (hc : c ≠ 0) :
    c.val = n + 1 -
      (τ (((n + 1) - (τ.symm ((n : ℕ) : ZMod (n + 1))).val : ℕ) : ZMod (n + 1))).val := by
  haveI : NeZero (n + 1) := ⟨by omega⟩
  set xₙ := τ.symm ((n : ℕ) : ZMod (n + 1)) with hxₙdef
  set yₙ := (((n + 1) - xₙ.val : ℕ) : ZMod (n + 1)) with hyₙdef
  have hτxₙ : τ xₙ = ((n : ℕ) : ZMod (n + 1)) := Equiv.apply_symm_apply τ _
  have hxₙ0 : xₙ ≠ 0 := by
    intro he
    have h1 : τ xₙ = 0 := by rw [he, hτ0]
    rw [hτxₙ] at h1
    have h2 : (((n : ℕ) : ZMod (n + 1))).val = 0 := by rw [h1, ZMod.val_zero]
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega : n < n + 1)] at h2
    omega
  have hxₙv : 1 ≤ xₙ.val := by
    by_contra h0
    have hz : xₙ.val = 0 := by omega
    apply hxₙ0
    have e := ZMod.natCast_zmod_val xₙ
    rw [hz, Nat.cast_zero] at e
    exact e.symm
  have hcv : 1 ≤ c.val := by
    by_contra h0
    have hz : c.val = 0 := by omega
    apply hc
    have e2 := ZMod.natCast_zmod_val c
    rw [hz, Nat.cast_zero] at e2
    exact e2.symm
  have hτyₙ0 : τ yₙ ≠ 0 := by
    intro he
    have h1 : yₙ = 0 := τ.injective (by rw [he, hτ0])
    have h2 : yₙ.val = 0 := by rw [h1, ZMod.val_zero]
    rw [hyₙdef, ZMod.val_natCast, Nat.mod_eq_of_lt (by have h3 := ZMod.val_lt xₙ; omega :
      (n + 1) - xₙ.val < n + 1)] at h2
    have h3 := ZMod.val_lt xₙ
    omega
  have hw1 : 1 ≤ (τ yₙ).val := by
    by_contra h0
    have hz : (τ yₙ).val = 0 := by omega
    apply hτyₙ0
    have e := ZMod.natCast_zmod_val (τ yₙ)
    rw [hz, Nat.cast_zero] at e
    exact e.symm
  have hstar := ExtParallel.star hτ0 h hxₙ0
  rw [← hyₙdef] at hstar
  have ha : (τ xₙ + c).val = c.val - 1 := by
    have e : τ xₙ + c = ((n + c.val : ℕ) : ZMod (n + 1)) := by
      rw [hτxₙ]
      conv_lhs => rw [← ZMod.natCast_zmod_val c]
      rw [← Nat.cast_add]
    rw [e, ZMod.val_natCast]
    have h1 : n + c.val = (c.val - 1) + (n + 1) := by omega
    rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by have h2 := ZMod.val_lt c; omega :
      c.val - 1 < n + 1)]
  have hb : (τ yₙ + c).val = ((τ yₙ).val + c.val) % (n + 1) := by
    have e : τ yₙ + c = (((τ yₙ).val + c.val : ℕ) : ZMod (n + 1)) := by
      conv_lhs => rw [← ZMod.natCast_zmod_val (τ yₙ), ← ZMod.natCast_zmod_val c]
      rw [← Nat.cast_add]
    rw [e, ZMod.val_natCast]
  rw [ha, hb] at hstar
  have hbnd : (τ yₙ).val + c.val < 2 * (n + 1) := by
    have h1 := ZMod.val_lt (τ yₙ)
    have h2 := ZMod.val_lt c
    omega
  have hpos : 2 ≤ (τ yₙ).val + c.val := by omega
  rcases hstar with h1 | ⟨-, h1⟩
  · -- `c.val - 1 + b = c.val + n + 1` forces `b = n + 2`, impossible
    have hblt : ((τ yₙ).val + c.val) % (n + 1) < n + 1 := Nat.mod_lt _ (by omega)
    omega
  · -- `c.val - 1 + b + 1 = c.val` forces `b = 0`, i.e. `(τ yₙ).val + c.val = n + 1`
    have hb0 : ((τ yₙ).val + c.val) % (n + 1) = 0 := by omega
    have hsum : (τ yₙ).val + c.val = n + 1 := by
      rcases Nat.lt_or_ge ((τ yₙ).val + c.val) (n + 1) with hlt | hge
      · rw [Nat.mod_eq_of_lt hlt] at hb0
        omega
      · have h2 : (τ yₙ).val + c.val = ((τ yₙ).val + c.val - (n + 1)) + (n + 1) := by
          omega
        rw [h2, Nat.add_mod_right,
          Nat.mod_eq_of_lt (by omega : (τ yₙ).val + c.val - (n + 1) < n + 1)] at hb0
        omega
    omega

/-- Uniqueness of the valid insertion parameter for a Type 1 labelling: any two
valid parameters agree (`c = 0` would force Type 2, and nonzero parameters have
a forced value). -/
theorem ExtParallel.unique {n : ℕ} (hn : 2 ≤ n) {τ : ZMod (n + 1) ≃ ZMod (n + 1)}
    (hτ : Beautiful τ) (hτ0 : τ 0 = 0) (hT : ¬ Type2 τ) {c₁ c₂ : ZMod (n + 1)}
    (h1 : ExtParallel τ c₁) (h2 : ExtParallel τ c₂) : c₁ = c₂ := by
  have hc1 : c₁ ≠ 0 := fun h0 => hT (type2_of_extParallel_zero hn hτ hτ0 (h0 ▸ h1))
  have hc2 : c₂ ≠ 0 := fun h0 => hT (type2_of_extParallel_zero hn hτ hτ0 (h0 ▸ h2))
  have e1 := val_eq_of_extParallel_ne_zero hn hτ0 h1 hc1
  have e2 := val_eq_of_extParallel_ne_zero hn hτ0 h2 hc2
  apply ZMod.val_injective (n + 1)
  rw [e1, e2]

/-- The fiber count: a normalized beautiful labelling of `[0, n]` has exactly one
beautiful normalized extension to `[0, n + 1]` if it is nonlinear, and exactly two if
it is linear. This is the combinatorial heart of the proof (the "Type 1 / Type 2"
dichotomy of the official solution). -/
theorem fiber_count {n : ℕ} (hn : 2 ≤ n) (τ : ZMod (n + 1) ≃ ZMod (n + 1))
    (hτ : Beautiful τ) (hτ0 : τ 0 = 0) :
    Fintype.card {c : ZMod (n + 1) // Beautiful (InsertNorm τ c)} =
      if Linear τ then 2 else 1 := by
  classical
  haveI : NeZero (n + 1) := ⟨by omega⟩
  rw [Fintype.card_subtype]
  have key : (Finset.univ.filter fun c : ZMod (n + 1) => Beautiful (InsertNorm τ c)) =
      (Finset.univ.filter fun c : ZMod (n + 1) => ExtParallel τ c) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨Beautiful.extParallel, ExtParallel.beautiful hτ⟩
  rw [key]
  by_cases hlin : Linear τ
  · rw [if_pos hlin]
    have hset : (Finset.univ.filter fun c : ZMod (n + 1) => ExtParallel τ c) = {0, -1} := by
      ext c
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · intro h
        rcases lin_unique hn hτ hτ0 hlin h with h0 | h0
        · exact Or.inl h0
        · exact Or.inr h0
      · rintro (rfl | rfl)
        · exact lin_valid_zero hn hlin
        · exact lin_valid_neg hn hlin
    rw [hset]
    rw [Finset.card_insert_of_notMem (by
      simp only [Finset.mem_singleton]
      intro h
      have e := congrArg ZMod.val h
      rw [ZMod.val_zero] at e
      have e2 : ((-1 : ZMod (n + 1))).val = n := by
        have h1 : (-1 : ZMod (n + 1)) = ((n : ℕ) : ZMod (n + 1)) := by
          rw [neg_eq_iff_add_eq_zero,
            show (1 : ZMod (n + 1)) = ((1 : ℕ) : ZMod (n + 1)) from by rw [Nat.cast_one],
            ← Nat.cast_add, show 1 + n = n + 1 from by omega, ZMod.natCast_self]
        rw [h1, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega : n < n + 1)]
      rw [e2] at e
      omega), Finset.card_singleton]
  · rw [if_neg hlin]
    have hT : ¬ Type2 τ := fun hT2 => hlin (type2_lin hn hτ hτ0 hT2)
    obtain ⟨c₀, hc₀⟩ := ExtParallel.exists hn hτ hτ0
    have hset : (Finset.univ.filter fun c : ZMod (n + 1) => ExtParallel τ c) = {c₀} := by
      ext c
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ⟨fun h => ExtParallel.unique hn hτ hτ0 hT h hc₀, fun h => by rw [h]; exact hc₀⟩
    rw [hset, Finset.card_singleton]


/-- The counting equivalence between normalized beautiful labellings of `[0, n + 1]`
and pairs of a normalized beautiful labelling of `[0, n]` and a valid insertion
parameter. -/
def countEquiv {n : ℕ} :
    {S : ZMod (n + 2) ≃ ZMod (n + 2) // Beautiful S ∧ S 0 = 0} ≃
    {τc : (Σ _τ : ZMod (n + 1) ≃ ZMod (n + 1), ZMod (n + 1)) //
      Beautiful τc.1 ∧ τc.1 0 = 0 ∧ Beautiful (InsertNorm τc.1 τc.2)} where
  toFun S := ⟨⟨DelNorm S.1, (Del S.1) 0⟩, DelNorm_beautiful S.2.1, DelNorm_zero S.1, by
    rw [InsertNorm_DelNorm S.1 S.2.2]
    exact S.2.1⟩
  invFun τc := ⟨InsertNorm τc.1.1 τc.1.2, τc.2.2.2, InsertNorm_zero _ _⟩
  left_inv S := Subtype.ext (InsertNorm_DelNorm S.1 S.2.2)
  right_inv τc := Subtype.ext (Sigma.ext (DelNorm_InsertNorm τc.1.1 τc.1.2 τc.2.2.1)
    (heq_of_eq (Del_InsertNorm_zero τc.1.1 τc.1.2 τc.2.2.1)))

/-- The number of beautiful labellings up to rotation. Every rotation class of
labellings contains a unique representative with `σ 0 = 0`, so this is the number `M`
of the problem. -/
def beautifulCount (n : ℕ) : ℕ :=
  Fintype.card {σ : ZMod (n + 1) ≃ ZMod (n + 1) // Beautiful σ ∧ σ 0 = 0}

/-- The number of ordered pairs of positive integers `(x, y)` with `x + y ≤ n` and
`gcd(x, y) = 1`: this is the number `N` of the problem. -/
def pairCount (n : ℕ) : ℕ :=
  (((Icc 1 n) ×ˢ (Icc 1 n)).filter fun p : ℕ × ℕ => p.1 + p.2 ≤ n ∧ p.1.Coprime p.2).card

/-! ## The pair-counting side -/

theorem pairCount_succ {n : ℕ} (hn : 2 ≤ n) :
    pairCount (n + 1) = pairCount n + (n + 1).totient := by
  classical
  rw [Nat.totient_eq_card_coprime]
  unfold pairCount
  set F : Finset (ℕ × ℕ) := ((Icc 1 (n + 1)) ×ˢ (Icc 1 (n + 1))).filter
      (fun p : ℕ × ℕ => p.1 + p.2 ≤ (n + 1) ∧ p.1.Coprime p.2) with hF
  rw [← Finset.card_filter_add_card_filter_not (s := F)
    (p := fun p : ℕ × ℕ => p.1 + p.2 ≤ n)]
  have hfirst : F.filter (fun p : ℕ × ℕ => p.1 + p.2 ≤ n) =
      ((Icc 1 n) ×ˢ (Icc 1 n)).filter (fun p : ℕ × ℕ => p.1 + p.2 ≤ n ∧ p.1.Coprime p.2) := by
    ext ⟨x, y⟩
    simp only [hF, mem_filter, mem_product, mem_Icc]
    generalize x.Coprime y = c
    constructor
    · rintro ⟨⟨⟨⟨hx1, hx2⟩, hy1, hy2⟩, ⟨hsum, hc⟩⟩, hle⟩
      exact ⟨⟨⟨hx1, by omega⟩, by omega, by omega⟩, hle, hc⟩
    · rintro ⟨⟨⟨hx1, hx2⟩, hy1, hy2⟩, hle, hc⟩
      exact ⟨⟨⟨⟨hx1, by omega⟩, by omega, by omega⟩, ⟨by omega, hc⟩⟩, hle⟩
  rw [hfirst]
  congr 1
  apply Finset.card_bij (fun p _ => p.1)
  · rintro ⟨x, y⟩ hp
    simp only [hF, mem_filter, mem_product, mem_Icc] at hp
    have hxy : x + y = n + 1 := by omega
    rw [mem_filter, mem_range]
    refine ⟨by omega, ?_⟩
    rw [Nat.coprime_comm, ← hxy, add_comm x y, Nat.coprime_add_self_right]
    exact hp.1.2.2
  · rintro ⟨x1, y1⟩ h1 ⟨x2, y2⟩ h2 heq
    simp only [hF, mem_filter, mem_product, mem_Icc] at h1 h2
    have e1 : x1 + y1 = n + 1 := by omega
    have e2 : x2 + y2 = n + 1 := by omega
    simp only at heq
    obtain rfl : y1 = y2 := by omega
    obtain rfl : x1 = x2 := heq
    rfl
  · intro a ha
    rw [mem_filter, mem_range] at ha
    obtain ⟨ha1, ha2⟩ := ha
    have ha0 : 1 ≤ a := by
      rcases Nat.eq_zero_or_pos a with h | h
      · exfalso
        rw [h, Nat.coprime_zero_right] at ha2
        omega
      · exact h
    refine ⟨(a, n + 1 - a), ?_, rfl⟩
    have han : a ≤ n + 1 := by omega
    simp only [hF, mem_filter, mem_product, mem_Icc]
    refine ⟨⟨⟨⟨ha0, han⟩, ⟨by omega, by omega⟩⟩, ⟨by omega, ?_⟩⟩, by omega⟩
    show Nat.Coprime a (n + 1 - a)
    exact (Nat.coprime_sub_self_right han).mpr (Nat.coprime_comm.mp ha2)

theorem pairCount_two : pairCount 2 = 1 := by
  decide

/-! ## The beautiful-counting side -/

theorem beautifulCount_two : beautifulCount 2 = 2 := by
  decide

/-- The key recurrence: the number of beautiful labellings of `[0, n + 1]` up to
rotation is the number for `[0, n]` plus `φ (n + 1)`. Proved by deleting the largest
label: every beautiful labelling of `[0, n]` has exactly one beautiful extension if
it is nonlinear (Type 1) and exactly two if it is linear (Type 2), and there are
exactly `φ (n + 1)` linear ones. -/
theorem beautifulCount_succ {n : ℕ} (hn : 2 ≤ n) :
    beautifulCount (n + 1) = beautifulCount n + (n + 1).totient := by
  classical
  unfold beautifulCount
  rw [Fintype.card_congr countEquiv, Fintype.card_subtype]
  have hs : (Finset.univ.filter fun τc : (Σ τ : ZMod (n + 1) ≃ ZMod (n + 1), ZMod (n + 1)) =>
      Beautiful τc.1 ∧ τc.1 0 = 0 ∧ Beautiful (InsertNorm τc.1 τc.2)) =
    (Finset.univ.filter fun τ : ZMod (n + 1) ≃ ZMod (n + 1) => Beautiful τ ∧ τ 0 = 0).sigma
      fun τ => Finset.univ.filter fun c : ZMod (n + 1) => Beautiful (InsertNorm τ c) := by
    ext ⟨τ, c⟩
    simp only [Finset.mem_filter, Finset.mem_univ, Finset.mem_sigma, true_and, and_assoc]
  rw [hs, Finset.card_sigma]
  have h2 : ∀ τ ∈ (Finset.univ.filter fun τ : ZMod (n + 1) ≃ ZMod (n + 1) =>
        Beautiful τ ∧ τ 0 = 0),
      (Finset.univ.filter fun c : ZMod (n + 1) => Beautiful (InsertNorm τ c)).card =
        if Linear τ then 2 else 1 := by
    intro τ hτ
    rw [Finset.mem_filter] at hτ
    rw [← Fintype.card_subtype]
    exact fiber_count hn τ hτ.2.1 hτ.2.2
  rw [Finset.sum_congr rfl h2]
  have hsplit : ∀ τ : ZMod (n + 1) ≃ ZMod (n + 1),
      (if Linear τ then 2 else 1) = 1 + (if Linear τ then 1 else 0) := by
    intro τ
    split <;> omega
  rw [Finset.sum_congr rfl (fun τ _ => hsplit τ), Finset.sum_add_distrib, Finset.sum_const,
    smul_eq_mul, mul_one, ← Finset.card_filter, Finset.filter_filter, linear_count hn,
    Fintype.card_subtype]

snip end

problem imo2013_p6 (n : ℕ) (hn : 3 ≤ n) :
    beautifulCount n = pairCount n + 1 := by
  have key : ∀ m : ℕ, 2 ≤ m → beautifulCount m = pairCount m + 1 := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => rw [beautifulCount_two, pairCount_two]
    | succ k hk ih =>
      rw [beautifulCount_succ hk, pairCount_succ hk, ih]
      omega
  exact key n (by omega)

end Imo2013P6

