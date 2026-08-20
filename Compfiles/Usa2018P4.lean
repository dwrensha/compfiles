/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Ring.Basic
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics, .NumberTheory] }

/-!
# USA Mathematical Olympiad 2018, Problem 4

Let p be a prime, and let a₁, ..., aₚ be integers. Show that there exists an integer k
such that the numbers

  a₁ + k, a₂ + 2k, ..., aₚ + pk

produce at least ½p distinct remainders upon division by p.
-/

namespace Usa2018P4

open Finset

snip begin

/-!
### Solution overview

For each residue `k` mod `p`, consider the ordered pairs `(i, j)` of distinct indices
for which `aᵢ + ik ≡ aⱼ + jk (mod p)`. Since `p` is prime, `j - i` is invertible
mod `p`, so each pair collides for exactly one `k`. Summing the number of collisions
over the `p` possible values of `k` therefore counts every one of the `p * (p - 1)`
ordered pairs once, whence some `k` has fewer than `p` colliding ordered pairs.
On the other hand, if `N` distinct values are attained and `C` ordered pairs collide,
then grouping by fibers shows `C + 2 * N ≥ 2 * p` (a fiber of size `n` contributes
`n * (n - 1)` collisions, and `n * (n - 1) + 2 ≥ 2 * n` for `n ≥ 1`). Combining,
`2 * N ≥ 2 * p - C > 2 * p - p = p`, so at least `p / 2` distinct remainders occur.
-/

variable {p : ℕ}

/-- The number of ordered pairs of distinct elements of a finset, in additive form. -/
lemma card_filter_ne_product {α : Type*} [DecidableEq α] (s : Finset α) :
    ((s ×ˢ s).filter (fun ij : α × α ↦ ij.1 ≠ ij.2)).card + s.card = s.card * s.card := by
  have hsd : (s ×ˢ s).filter (fun ij : α × α ↦ ij.1 ≠ ij.2) = (s ×ˢ s) \ s.diag := by
    ext ⟨x, y⟩
    simp only [mem_filter, mem_product, mem_diag, mem_sdiff]
    constructor
    · rintro ⟨⟨hx, hy⟩, hxy⟩
      exact ⟨⟨hx, hy⟩, fun h ↦ hxy h.2⟩
    · rintro ⟨⟨hx, hy⟩, h⟩
      exact ⟨⟨hx, hy⟩, fun hxy ↦ h ⟨hx, hxy⟩⟩
  have hsub : s.diag ⊆ s ×ˢ s := by
    intro x hx
    rw [mem_diag] at hx
    exact mem_product.mpr ⟨hx.1, hx.2 ▸ hx.1⟩
  rw [hsd]
  have h := card_sdiff_add_card_eq_card hsub
  rw [diag_card, card_product] at h
  exact h

variable (a : Fin p → ZMod p)

/-- The values `aᵢ + ik` (computed in `ZMod p`) produced by the shift `k`. -/
def f (k : ZMod p) (i : Fin p) : ZMod p := a i + ((i : ℕ) : ZMod p) * k

/-- The unique residue `k` mod `p` for which the pair `(i, j)` collides
(this is well-defined when `i ≠ j` and `p` is prime). -/
def phi (ij : Fin p × Fin p) : ZMod p :=
  (a ij.1 - a ij.2) * (((ij.2 : ℕ) : ZMod p) - ((ij.1 : ℕ) : ZMod p))⁻¹

/-- Ordered pairs of distinct indices whose values collide for the shift `k`. -/
def F (k : ZMod p) : Finset (Fin p × Fin p) :=
  Finset.univ.filter (fun ij ↦ ij.1 ≠ ij.2 ∧ f a k ij.1 = f a k ij.2)

/-- All ordered pairs of distinct indices. -/
def S : Finset (Fin p × Fin p) := Finset.univ.filter (fun ij ↦ ij.1 ≠ ij.2)

/-- The set of values attained by the shift `k`. -/
def im (k : ZMod p) : Finset (ZMod p) := Finset.univ.image (f a k)

/-- The fiber over `v` of the value map of the shift `k`. -/
def fib (k : ZMod p) (v : ZMod p) : Finset (Fin p) :=
  Finset.univ.filter (fun i ↦ f a k i = v)

lemma cast_ne_of_ne {i j : Fin p} (hij : i ≠ j) :
    ((i : ℕ) : ZMod p) ≠ ((j : ℕ) : ZMod p) := by
  intro h
  rw [ZMod.natCast_eq_natCast_iff] at h
  exact hij (Fin.ext (Nat.ModEq.eq_of_lt_of_lt h i.is_lt j.is_lt))

/-- The pair `(i, j)` collides for the shift `k` iff `k = phi a (i, j)`. -/
lemma f_eq_iff_phi_eq (hp : p.Prime) (k : ZMod p) {i j : Fin p} (hij : i ≠ j) :
    f a k i = f a k j ↔ phi a (i, j) = k := by
  have : Fact p.Prime := ⟨hp⟩
  have hne : ((j : ℕ) : ZMod p) - ((i : ℕ) : ZMod p) ≠ 0 :=
    sub_ne_zero.mpr (cast_ne_of_ne hij.symm)
  show a i + ((i : ℕ) : ZMod p) * k = a j + ((j : ℕ) : ZMod p) * k ↔
    (a i - a j) * (((j : ℕ) : ZMod p) - ((i : ℕ) : ZMod p))⁻¹ = k
  constructor
  · intro h
    have h2 : a i - a j = k * (((j : ℕ) : ZMod p) - ((i : ℕ) : ZMod p)) := by
      linear_combination h
    rw [h2]
    exact mul_inv_cancel_right₀ hne k
  · intro h
    have h3 : (a i - a j) * (((j : ℕ) : ZMod p) - ((i : ℕ) : ZMod p))⁻¹ *
        (((j : ℕ) : ZMod p) - ((i : ℕ) : ZMod p)) = a i - a j :=
      inv_mul_cancel_right₀ hne (a i - a j)
    rw [h] at h3
    linear_combination -h3

/-- There are `p * (p - 1)` ordered pairs of distinct indices (additive form). -/
lemma card_S_add : (S : Finset (Fin p × Fin p)).card + p = p * p := by
  have h := card_filter_ne_product (Finset.univ : Finset (Fin p))
  rw [univ_product_univ, card_univ, Fintype.card_fin] at h
  exact h

/-- Every ordered pair collides for exactly one shift `k`, hence the collision counts
over all shifts sum to the number of ordered pairs. -/
lemma sum_card_F_add [NeZero p] (hp : p.Prime) :
    (∑ k : ZMod p, (F a k).card) + p = p * p := by
  have hF : ∀ k : ZMod p,
      F a k = (S : Finset (Fin p × Fin p)).filter (fun ij ↦ phi a ij = k) := by
    intro k
    ext ⟨i, j⟩
    simp only [F, S, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨hij, h⟩
      exact ⟨hij, (f_eq_iff_phi_eq a hp k hij).mp h⟩
    · rintro ⟨hij, h⟩
      exact ⟨hij, (f_eq_iff_phi_eq a hp k hij).mpr h⟩
  have hsum : (∑ k : ZMod p, (F a k).card) = (S : Finset (Fin p × Fin p)).card :=
    calc (∑ k : ZMod p, (F a k).card)
        = ∑ k : ZMod p, ((S : Finset (Fin p × Fin p)).filter
            (fun ij ↦ phi a ij = k)).card :=
          sum_congr rfl (fun k _ ↦ congrArg Finset.card (hF k))
      _ = (S : Finset (Fin p × Fin p)).card :=
          (card_eq_sum_card_fiberwise (s := S) (t := (Finset.univ : Finset (ZMod p)))
            (f := phi a) (fun _ _ ↦ mem_univ _)).symm
  rw [hsum]
  exact card_S_add

/-- Pigeonhole: some shift `k` has fewer than `p` colliding ordered pairs. -/
lemma exists_F_card_lt (hp : p.Prime) : ∃ k : ZMod p, (F a k).card < p := by
  have : NeZero p := ⟨hp.pos.ne'⟩
  by_contra h
  push Not at h
  have h2 : p * p ≤ ∑ k : ZMod p, (F a k).card := by
    have hle : ∑ k : ZMod p, p ≤ ∑ k : ZMod p, (F a k).card :=
      sum_le_sum (fun k _ ↦ h k)
    rw [sum_const, card_univ, ZMod.card, smul_eq_mul] at hle
    exact hle
  have h3 := sum_card_F_add a hp
  have hp0 : 0 < p := hp.pos
  lia

/-- If `N` distinct values are attained and `C` ordered pairs collide, then
`2 * p ≤ C + 2 * N`: writing `nᵥ ≥ 1` for the fiber sizes we have `p = Σ nᵥ`,
`N = Σ 1` and `C = Σ nᵥ (nᵥ - 1)`, and `n * (n - 1) + 2 ≥ 2 * n` for `n ≥ 1`. -/
lemma two_mul_le_card_F_add (k : ZMod p) :
    2 * p ≤ (F a k).card + 2 * (im a k).card := by
  have hpsum : p = ∑ v ∈ im a k, (fib a k v).card := by
    have h := card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Fin p)))
      (t := im a k) (f := f a k) (fun i _ ↦ mem_image_of_mem (f a k) (mem_univ i))
    rw [card_univ, Fintype.card_fin] at h
    exact h
  have hfiber : ∀ v : ZMod p, (F a k).filter (fun ij ↦ f a k ij.1 = v) =
      ((fib a k v) ×ˢ (fib a k v)).filter (fun ij : Fin p × Fin p ↦ ij.1 ≠ ij.2) := by
    intro v
    ext ⟨i, j⟩
    simp only [F, fib, mem_filter, mem_univ, true_and, mem_product]
    constructor
    · rintro ⟨⟨hij, h1⟩, h2⟩
      exact ⟨⟨h2, h1 ▸ h2⟩, hij⟩
    · rintro ⟨⟨h2, h3⟩, hij⟩
      exact ⟨⟨hij, h2.trans h3.symm⟩, h2⟩
  have hFcard : (F a k).card = ∑ v ∈ im a k,
      (((fib a k v) ×ˢ (fib a k v)).filter
        (fun ij : Fin p × Fin p ↦ ij.1 ≠ ij.2)).card := by
    refine (card_eq_sum_card_fiberwise (s := F a k) (t := im a k)
      (f := fun ij ↦ f a k ij.1)
      (fun ij _ ↦ mem_image_of_mem (f a k) (mem_univ ij.1))).trans ?_
    exact sum_congr rfl (fun v _ ↦ congrArg Finset.card (hfiber v))
  have hterm : ∀ v ∈ im a k, 2 * (fib a k v).card ≤
      (((fib a k v) ×ˢ (fib a k v)).filter
        (fun ij : Fin p × Fin p ↦ ij.1 ≠ ij.2)).card + 2 := by
    intro v hv
    have hne : (fib a k v).Nonempty := by
      obtain ⟨i, -, hi⟩ := mem_image.mp hv
      exact ⟨i, mem_filter.mpr ⟨mem_univ i, hi⟩⟩
    have hcount := card_filter_ne_product (fib a k v)
    have h1 : 1 ≤ (fib a k v).card := card_pos.mpr hne
    have key : ∀ c n : ℕ, 1 ≤ n → c + n = n * n → 2 * n ≤ c + 2 := by
      intro c n _hn hcn
      rcases n with _ | m
      · lia
      · have hm : m ≤ m * m := by
          rcases m with _ | m
          · simp
          · exact Nat.le_mul_of_pos_right (m + 1) (Nat.succ_pos m)
        have hexp : (m + 1) * (m + 1) = m * m + 2 * m + 1 := by ring
        lia
    exact key _ _ h1 hcount
  have h2p : 2 * p = ∑ v ∈ im a k, 2 * (fib a k v).card := by
    have h : 2 * p = 2 * ∑ v ∈ im a k, (fib a k v).card := congrArg (2 * ·) hpsum
    rw [Finset.mul_sum] at h
    exact h
  have him2 : 2 * (im a k).card = ∑ v ∈ im a k, 2 := by
    rw [sum_const, smul_eq_mul, mul_comm]
  rw [h2p, hFcard, him2, ← sum_add_distrib]
  exact sum_le_sum hterm

snip end

/-- We index by `Fin p` instead of `{1, ..., p}` (the map `i ↦ i mod p` is a bijection
`{1, ..., p} ≃ Fin p` sending `p ↦ 0`, and `p * k ≡ 0 (mod p)`, so the families of
remainders coincide), we work directly with remainders in `ZMod p`, and the conclusion
`p ≤ 2 * N` is the integral form of "`N ≥ p / 2` distinct remainders". -/
problem usa2018_p4 (p : ℕ) (hp : p.Prime) (a : Fin p → ℤ) :
    ∃ k : ℤ, p ≤ 2 * (Finset.univ.image fun i : Fin p ↦
      (a i : ZMod p) + ((i : ℕ) : ZMod p) * (k : ZMod p)).card := by
  obtain ⟨K, hK⟩ := exists_F_card_lt (fun i ↦ (a i : ZMod p)) hp
  have hineq := two_mul_le_card_F_add (fun i ↦ (a i : ZMod p)) K
  have hcomb : p ≤ 2 * (im (fun i ↦ (a i : ZMod p)) K).card := by lia
  refine ⟨ZMod.cast K, ?_⟩
  rw [ZMod.intCast_zmod_cast]
  exact hcomb

end Usa2018P4
