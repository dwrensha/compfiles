/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Data.Int.ConditionallyCompleteOrder
public import Mathlib.Data.Int.Star
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics] }

/-!
# USA Mathematical Olympiad 1987, Problem 5

a₁, a₂, ... , aₙ is a sequence of 0s and 1s. T is the number of triples
(aᵢ, aⱼ, aₖ) with i < j < k which are not equal to (0, 1, 0) or (1, 0, 1).
For 1 ≤ i ≤ n, f(i) is the number of j < i with aⱼ = aᵢ plus the number of
j > i with aⱼ ≠ aᵢ. Show that
T = f(1)(f(1) - 1)/2 + f(2)(f(2) - 1)/2 + ... + f(n)(f(n) - 1)/2.
If n is odd, what is the smallest value of T?
-/

namespace Usa1987P5

variable {n : ℕ}

/-- The set of positions `j < i` with `a j = a i`. -/
def eqBefore (a : Fin n → Bool) (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun j ↦ j < i ∧ a j = a i

/-- The set of positions `j > i` with `a j ≠ a i`. -/
def neqAfter (a : Fin n → Bool) (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun j ↦ i < j ∧ a j ≠ a i

/-- The quantity `f(i)` from the problem statement. -/
def f (a : Fin n → Bool) (i : Fin n) : ℕ := (eqBefore a i).card + (neqAfter a i).card

/-- The quantity `T` from the problem statement: the number of triples of
indices `i < j < k` whose values are not `(0, 1, 0)` or `(1, 0, 1)`. -/
def numGoodTriples (a : Fin n → Bool) : ℕ :=
  (Finset.univ.filter fun t : Fin n × Fin n × Fin n ↦
    t.1 < t.2.1 ∧ t.2.1 < t.2.2 ∧
      ¬ ((a t.1 = false ∧ a t.2.1 = true ∧ a t.2.2 = false) ∨
         (a t.1 = true ∧ a t.2.1 = false ∧ a t.2.2 = true))).card

/-- The alternating sequence `0, 1, 0, 1, ...`. -/
def altSeq (n : ℕ) : Fin n → Bool := fun i ↦ (i : ℕ) % 2 == 1

determine minT : ℕ → ℕ := fun n ↦ n * (n - 1) * (n - 3) / 8

snip begin

lemma f_apply (a : Fin n → Bool) (i : Fin n) :
    f a i = (eqBefore a i).card + (neqAfter a i).card := rfl

/-- A triple of bits is good (not alternating) iff two adjacent values agree. -/
lemma good_iff (x y z : Bool) :
    ¬ ((x = false ∧ y = true ∧ z = false) ∨ (x = true ∧ y = false ∧ z = true)) ↔
      x = y ∨ y = z := by
  cases x <;> cases y <;> cases z <;> decide

/-- Vandermonde's identity at `k = 2`. -/
lemma choose_add_two (x y : ℕ) : (x + y).choose 2 = x.choose 2 + y.choose 2 + x * y := by
  have key : (((x + y).choose 2 : ℕ) : ℚ) = ((x.choose 2 + y.choose 2 + x * y : ℕ) : ℚ) := by
    push_cast [Nat.cast_choose_two]
    ring
  exact_mod_cast key

/-- Triples `i < j < k` with `a i = a j = a k`. -/
def tripsA (a : Fin n → Bool) : Finset (Fin n × Fin n × Fin n) :=
  Finset.univ.filter fun t ↦ t.1 < t.2.1 ∧ t.2.1 < t.2.2 ∧ a t.1 = a t.2.1 ∧ a t.2.1 = a t.2.2

/-- Triples `i < j < k` with `a i = a j ≠ a k`. -/
def tripsB (a : Fin n → Bool) : Finset (Fin n × Fin n × Fin n) :=
  Finset.univ.filter fun t ↦ t.1 < t.2.1 ∧ t.2.1 < t.2.2 ∧ a t.1 = a t.2.1 ∧ a t.2.1 ≠ a t.2.2

/-- Triples `i < j < k` with `a i ≠ a j = a k`. -/
def tripsC (a : Fin n → Bool) : Finset (Fin n × Fin n × Fin n) :=
  Finset.univ.filter fun t ↦ t.1 < t.2.1 ∧ t.2.1 < t.2.2 ∧ a t.1 ≠ a t.2.1 ∧ a t.2.1 = a t.2.2

lemma numGoodTriples_eq (a : Fin n → Bool) :
    numGoodTriples a = (tripsA a).card + (tripsB a).card + (tripsC a).card := by
  have hset : (Finset.univ.filter fun t : Fin n × Fin n × Fin n ↦
      t.1 < t.2.1 ∧ t.2.1 < t.2.2 ∧
        ¬ ((a t.1 = false ∧ a t.2.1 = true ∧ a t.2.2 = false) ∨
           (a t.1 = true ∧ a t.2.1 = false ∧ a t.2.2 = true))) =
      tripsA a ∪ tripsB a ∪ tripsC a := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, tripsA, tripsB, tripsC,
      Finset.mem_union]
    rw [good_iff]
    constructor
    · rintro ⟨h1, h2, h⟩
      rcases eq_or_ne (a t.1) (a t.2.1) with h01 | h01
      · rcases eq_or_ne (a t.2.1) (a t.2.2) with h12 | h12
        · exact Or.inl (Or.inl ⟨h1, h2, h01, h12⟩)
        · exact Or.inl (Or.inr ⟨h1, h2, h01, h12⟩)
      · rcases h with h | h
        · exact absurd h h01
        · exact Or.inr ⟨h1, h2, h01, h⟩
    · rintro ((⟨h1, h2, h01, h12⟩ | ⟨h1, h2, h01, h12⟩) | ⟨h1, h2, h01, h12⟩)
      · exact ⟨h1, h2, Or.inl h01⟩
      · exact ⟨h1, h2, Or.inl h01⟩
      · exact ⟨h1, h2, Or.inr h12⟩
  have hdis1 : Disjoint (tripsA a ∪ tripsB a) (tripsC a) := by
    apply Finset.disjoint_left.mpr
    intro t htAB htC
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, tripsA, tripsB,
      tripsC] at htAB htC
    rcases htAB with htA | htB
    · exact htC.2.2.1 htA.2.2.1
    · exact htC.2.2.1 htB.2.2.1
  have hdis2 : Disjoint (tripsA a) (tripsB a) := by
    apply Finset.disjoint_left.mpr
    intro t htA htB
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, tripsA, tripsB] at htA htB
    exact htB.2.2.2 htA.2.2.2
  unfold numGoodTriples
  rw [hset, Finset.card_union_of_disjoint hdis1, Finset.card_union_of_disjoint hdis2]

lemma card_tripsA (a : Fin n → Bool) :
    (tripsA a).card = ∑ k : Fin n, ((eqBefore a k).card).choose 2 := by
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun t : Fin n × Fin n × Fin n ↦ t.2.2) (t := Finset.univ) (by simp)]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [← Finset.card_product_filter_lt]
  apply Finset.card_bij (fun t _ ↦ (t.1, t.2.1))
  · intro t ht
    simp only [Finset.mem_filter, tripsA, Finset.mem_univ, true_and] at ht
    obtain ⟨⟨h1, h2, h3, h4⟩, h5⟩ := ht
    simp only [Finset.mem_filter, Finset.mem_product, eqBefore, Finset.mem_univ, true_and]
    refine ⟨⟨⟨h1.trans (h2.trans_le h5.le), ?_⟩, ⟨h2.trans_le h5.le, ?_⟩⟩, h1⟩
    · rw [← h5]; exact h3.trans h4
    · rw [← h5]; exact h4
  · intro t₁ ht₁ t₂ ht₂ heq
    simp only [Finset.mem_filter] at ht₁ ht₂
    obtain ⟨-, h5₁⟩ := ht₁
    obtain ⟨-, h5₂⟩ := ht₂
    rw [Prod.ext_iff] at heq
    exact Prod.ext heq.1 (Prod.ext heq.2 (h5₁.trans h5₂.symm))
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product, eqBefore, Finset.mem_univ,
      true_and] at hp
    obtain ⟨⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩, h5⟩ := hp
    refine ⟨(p.1, p.2, k), ?_, rfl⟩
    simp only [Finset.mem_filter, tripsA, Finset.mem_univ, true_and]
    exact ⟨⟨h5, h3, h2.trans h4.symm, h4⟩, trivial⟩

lemma card_tripsB (a : Fin n → Bool) :
    (tripsB a).card = ∑ j : Fin n, (eqBefore a j).card * (neqAfter a j).card := by
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun t : Fin n × Fin n × Fin n ↦ t.2.1) (t := Finset.univ) (by simp)]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [← Finset.card_product]
  apply Finset.card_bij (fun t _ ↦ (t.1, t.2.2))
  · intro t ht
    simp only [Finset.mem_filter, tripsB, Finset.mem_univ, true_and] at ht
    obtain ⟨⟨h1, h2, h3, h4⟩, h5⟩ := ht
    simp only [Finset.mem_product, eqBefore, neqAfter, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact ⟨⟨h5 ▸ h1, h5 ▸ h3⟩, ⟨h5 ▸ h2, (h5 ▸ h4).symm⟩⟩
  · intro t₁ ht₁ t₂ ht₂ heq
    simp only [Finset.mem_filter] at ht₁ ht₂
    obtain ⟨-, h5₁⟩ := ht₁
    obtain ⟨-, h5₂⟩ := ht₂
    rw [Prod.ext_iff] at heq
    exact Prod.ext heq.1 (Prod.ext (h5₁.trans h5₂.symm) heq.2)
  · intro p hp
    simp only [Finset.mem_product, eqBefore, neqAfter, Finset.mem_filter, Finset.mem_univ,
      true_and] at hp
    obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hp
    refine ⟨(p.1, j, p.2), ?_, rfl⟩
    simp only [Finset.mem_filter, tripsB, Finset.mem_univ, true_and]
    exact ⟨⟨h1, h3, h2, h4.symm⟩, trivial⟩

lemma card_tripsC (a : Fin n → Bool) :
    (tripsC a).card = ∑ i : Fin n, ((neqAfter a i).card).choose 2 := by
  have hbool : ∀ x y b : Bool, x ≠ b → y ≠ b → x = y := by decide
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun t : Fin n × Fin n × Fin n ↦ t.1) (t := Finset.univ) (by simp)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← Finset.card_product_filter_lt]
  apply Finset.card_bij (fun t _ ↦ (t.2.1, t.2.2))
  · intro t ht
    simp only [Finset.mem_filter, tripsC, Finset.mem_univ, true_and] at ht
    obtain ⟨⟨h1, h2, h3, h4⟩, h5⟩ := ht
    simp only [Finset.mem_filter, Finset.mem_product, neqAfter, Finset.mem_univ, true_and]
    exact ⟨⟨⟨h5 ▸ h1, (h5 ▸ h3).symm⟩, ⟨h5 ▸ (h1.trans h2), h5 ▸ (h4.symm.trans_ne h3.symm)⟩⟩, h2⟩
  · intro t₁ ht₁ t₂ ht₂ heq
    simp only [Finset.mem_filter] at ht₁ ht₂
    obtain ⟨-, h5₁⟩ := ht₁
    obtain ⟨-, h5₂⟩ := ht₂
    rw [Prod.ext_iff] at heq
    exact Prod.ext (h5₁.trans h5₂.symm) (Prod.ext heq.1 heq.2)
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product, neqAfter, Finset.mem_univ,
      true_and] at hp
    obtain ⟨⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩, h5⟩ := hp
    refine ⟨(i, p.1, p.2), ?_, rfl⟩
    simp only [Finset.mem_filter, tripsC, Finset.mem_univ, true_and]
    exact ⟨⟨h1, h5, h2.symm, hbool _ _ _ h2 h4⟩, trivial⟩

lemma sum_eqBefore (a : Fin n → Bool) :
    ∑ i : Fin n, (eqBefore a i).card =
      ((Finset.univ ×ˢ Finset.univ).filter fun p : Fin n × Fin n ↦
        p.1 < p.2 ∧ a p.1 = a p.2).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.snd) (t := Finset.univ) (by simp)]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  apply Finset.card_bij (fun i _ ↦ (i, j))
  · intro i hi
    simp only [eqBefore, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and]
    exact ⟨⟨hi.1, hi.2⟩, by simp⟩
  · intro i₁ _ i₂ _ heq
    rw [Prod.ext_iff] at heq
    exact heq.1
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and] at hp
    refine ⟨p.1, ?_, Prod.ext rfl hp.2.symm⟩
    simp only [eqBefore, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hp.2 ▸ hp.1.1, hp.2 ▸ hp.1.2⟩

lemma sum_neqAfter (a : Fin n → Bool) :
    ∑ i : Fin n, (neqAfter a i).card =
      ((Finset.univ ×ˢ Finset.univ).filter fun p : Fin n × Fin n ↦
        p.1 < p.2 ∧ a p.1 ≠ a p.2).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := Finset.univ) (by simp)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  apply Finset.card_bij (fun j' _ ↦ (i, j'))
  · intro j' hj'
    simp only [neqAfter, Finset.mem_filter, Finset.mem_univ, true_and] at hj'
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and]
    exact ⟨⟨hj'.1, hj'.2.symm⟩, by simp⟩
  · intro j₁ _ j₂ _ heq
    rw [Prod.ext_iff] at heq
    exact heq.2
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and] at hp
    refine ⟨p.2, ?_, Prod.ext hp.2.symm rfl⟩
    simp only [neqAfter, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hp.2 ▸ hp.1.1, (hp.2 ▸ hp.1.2).symm⟩

/-- The sum of the `f` values depends only on `n`. -/
lemma sum_f (a : Fin n → Bool) :
    ∑ i : Fin n, f a i = (Finset.univ : Finset (Fin n)).card.choose 2 := by
  have hsplit : ∑ i : Fin n, f a i =
      ∑ i : Fin n, (eqBefore a i).card + ∑ i : Fin n, (neqAfter a i).card := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [f_apply]
  rw [hsplit, sum_eqBefore, sum_neqAfter, ← Finset.card_product_filter_lt]
  have hdis : Disjoint
      ((Finset.univ ×ˢ Finset.univ).filter fun p : Fin n × Fin n ↦ p.1 < p.2 ∧ a p.1 = a p.2)
      ((Finset.univ ×ˢ Finset.univ).filter fun p : Fin n × Fin n ↦ p.1 < p.2 ∧ a p.1 ≠ a p.2) := by
    apply Finset.disjoint_left.mpr
    intro p hp1 hp2
    simp only [Finset.mem_filter] at hp1 hp2
    exact hp2.2.2 hp1.2.2
  rw [← Finset.card_union_of_disjoint hdis]
  congr 1
  ext p
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
    true_and]
  constructor
  · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
  · intro h
    rcases eq_or_ne (a p.1) (a p.2) with he | he
    · exact Or.inl ⟨h, he⟩
    · exact Or.inr ⟨h, he⟩

snip end

problem usa1987_p5_part1 (a : Fin n → Bool) :
    numGoodTriples a = ∑ i : Fin n, (f a i).choose 2 := by
  rw [numGoodTriples_eq, card_tripsA, card_tripsB, card_tripsC]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [f_apply, choose_add_two]
  ring

snip begin

/-- Divisibility: `n * (n - 1) * (n - 3) = 8 * (n * C((n-1)/2, 2))` for `n = 2k + 1`. -/
lemma key_div (k : ℕ) :
    (2 * k + 1) * ((2 * k + 1) - 1) * ((2 * k + 1) - 3) = 8 * ((2 * k + 1) * k.choose 2) := by
  have hk2 : 2 * k.choose 2 = k * (k - 1) := by
    rw [Nat.choose_two_right]
    have hev := Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self k)
    omega
  have e1 : (2 * k + 1 - 1 : ℕ) = 2 * k := by omega
  have e2 : (2 * k + 1 - 3 : ℕ) = 2 * (k - 1) := by omega
  rw [e1, e2]
  have h3 : (2 * k) * (2 * (k - 1)) = 8 * k.choose 2 := by
    have h4 : (2 * k) * (2 * (k - 1)) = 4 * (k * (k - 1)) := by
      generalize k - 1 = u
      ring
    rw [h4, ← hk2]
    ring
  calc (2 * k + 1) * (2 * k) * (2 * (k - 1))
      = (2 * k + 1) * ((2 * k) * (2 * (k - 1))) := by rw [mul_assoc]
    _ = (2 * k + 1) * (8 * k.choose 2) := by rw [h3]
    _ = 8 * ((2 * k + 1) * k.choose 2) := by ring

/-- Cast of the product `n * (n - 1) * (n - 3)` to the integers, for odd `n`. -/
lemma cast_key (k : ℕ) :
    (((2 * k + 1) * ((2 * k + 1) - 1) * ((2 * k + 1) - 3) : ℕ) : ℤ) =
      ((2 * k + 1 : ℕ) : ℤ) * (((2 * k + 1 : ℕ) : ℤ) - 1) * (((2 * k + 1 : ℕ) : ℤ) - 3) := by
  rcases k with _ | k
  · norm_num
  · have e1 : (2 * (k + 1) + 1 - 1 : ℕ) = 2 * (k + 1) := by omega
    have e2 : (2 * (k + 1) + 1 - 3 : ℕ) = 2 * k := by omega
    rw [e1, e2]
    push_cast
    ring

/-- The lower bound: every sequence on `2k + 1` positions has at least
`(2k + 1) * C(k, 2)` good triples. -/
lemma lower_bound (k : ℕ) (a : Fin (2 * k + 1) → Bool) :
    (2 * k + 1) * k.choose 2 ≤ numGoodTriples a := by
  have h2T : 2 * (numGoodTriples a : ℤ) =
      ∑ i : Fin (2 * k + 1), (f a i : ℤ) ^ 2 - ∑ i : Fin (2 * k + 1), (f a i : ℤ) := by
    have hp1 := usa1987_p5_part1 a
    have h : (2 : ℕ) * numGoodTriples a = ∑ i : Fin (2 * k + 1), (f a i) * ((f a i) - 1) := by
      rw [hp1, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [Nat.choose_two_right]
      have hev := Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self (f a i))
      omega
    have hcast : ((2 * numGoodTriples a : ℕ) : ℤ) = 2 * (numGoodTriples a : ℤ) := by
      push_cast; ring
    rw [← hcast, h, Nat.cast_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rcases eq_or_ne (f a i) 0 with h0 | h0
    · simp [h0]
    · have h1 : (1 : ℕ) ≤ f a i := Nat.one_le_iff_ne_zero.mpr h0
      rw [Nat.cast_mul, Nat.cast_sub h1]
      push_cast
      ring
  have h2sum : 2 * ∑ i : Fin (2 * k + 1), (f a i : ℤ) =
      ((2 * k + 1 : ℕ) : ℤ) * (((2 * k + 1 : ℕ) : ℤ) - 1) := by
    have hsf := sum_f a
    rw [Finset.card_univ, Fintype.card_fin] at hsf
    have h : (2 : ℕ) * ∑ i : Fin (2 * k + 1), f a i = (2 * k + 1) * ((2 * k + 1) - 1) := by
      rw [hsf, Nat.choose_two_right]
      have hev := Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self (2 * k + 1))
      omega
    have hcast : ((2 * ∑ i : Fin (2 * k + 1), f a i : ℕ) : ℤ) =
        2 * ∑ i : Fin (2 * k + 1), (f a i : ℤ) := by
      push_cast; ring
    rw [← hcast, h, Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ 2 * k + 1)]
    push_cast
    ring
  have hcs : (∑ i : Fin (2 * k + 1), (f a i : ℤ)) ^ 2 ≤
      ((2 * k + 1 : ℕ) : ℤ) * ∑ i : Fin (2 * k + 1), (f a i : ℤ) ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
      (f := fun i : Fin (2 * k + 1) ↦ (f a i : ℤ))
    rwa [Finset.card_univ, Fintype.card_fin] at h
  have hn' : (0 : ℤ) < ((2 * k + 1 : ℕ) : ℤ) := by positivity
  have hmain : ((2 * k + 1 : ℕ) : ℤ) * (8 * (numGoodTriples a : ℤ)) ≥
      ((2 * k + 1 : ℕ) : ℤ) * (((2 * k + 1 : ℕ) : ℤ) * (((2 * k + 1 : ℕ) : ℤ) - 1) *
        (((2 * k + 1 : ℕ) : ℤ) - 3)) := by
    have hsq : (2 * ∑ i : Fin (2 * k + 1), (f a i : ℤ)) ^ 2 =
        (((2 * k + 1 : ℕ) : ℤ) * (((2 * k + 1 : ℕ) : ℤ) - 1)) ^ 2 :=
      congrArg (· ^ 2) h2sum
    have hN : ((2 * k + 1 : ℕ) : ℤ) * (2 * ∑ i : Fin (2 * k + 1), (f a i : ℤ)) =
        ((2 * k + 1 : ℕ) : ℤ) * (((2 * k + 1 : ℕ) : ℤ) * (((2 * k + 1 : ℕ) : ℤ) - 1)) :=
      congrArg (((2 * k + 1 : ℕ) : ℤ) * ·) h2sum
    nlinarith [hcs, h2T, h2sum, hsq, hN]
  have h8 : (8 : ℤ) * (numGoodTriples a : ℤ) ≥
      ((2 * k + 1 : ℕ) : ℤ) * (((2 * k + 1 : ℕ) : ℤ) - 1) * (((2 * k + 1 : ℕ) : ℤ) - 3) :=
    le_of_mul_le_mul_left hmain hn'
  have hcastk := cast_key k
  rw [key_div k] at hcastk
  rw [← hcastk] at h8
  push_cast at h8
  have h9 : (((2 * k + 1) * k.choose 2 : ℕ) : ℤ) ≤ (numGoodTriples a : ℤ) :=
    le_of_mul_le_mul_left h8 (by norm_num)
  exact_mod_cast h9

lemma altSeq_eq_iff {i j : Fin n} : altSeq n i = altSeq n j ↔ (i : ℕ) % 2 = (j : ℕ) % 2 := by
  have hi := Nat.mod_lt (i : ℕ) (show 0 < 2 by norm_num)
  have hj := Nat.mod_lt (j : ℕ) (show 0 < 2 by norm_num)
  simp only [altSeq]
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  constructor <;> omega

lemma card_eqBefore_alt (k : ℕ) (i : Fin (2 * k + 1)) :
    (eqBefore (altSeq (2 * k + 1)) i).card = (i : ℕ) / 2 := by
  have h2 : (i : ℕ) % 2 < 2 := Nat.mod_lt _ (by norm_num)
  rw [← Finset.card_range ((i : ℕ) / 2)]
  apply Finset.card_bij (fun (j : Fin (2 * k + 1)) _ ↦ (j : ℕ) / 2)
  · intro j hj
    simp only [eqBefore, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    have hpar : (j : ℕ) % 2 = (i : ℕ) % 2 := altSeq_eq_iff.mp hj.2
    have hlt : (j : ℕ) < (i : ℕ) := hj.1
    simp only [Finset.mem_range]
    omega
  · intro j₁ hj₁ j₂ hj₂ heq
    simp only [eqBefore, Finset.mem_filter, Finset.mem_univ, true_and] at hj₁ hj₂
    have hpar1 : (j₁ : ℕ) % 2 = (i : ℕ) % 2 := altSeq_eq_iff.mp hj₁.2
    have hpar2 : (j₂ : ℕ) % 2 = (i : ℕ) % 2 := altSeq_eq_iff.mp hj₂.2
    have heq2 : (j₁ : ℕ) / 2 = (j₂ : ℕ) / 2 := heq
    apply Fin.ext
    omega
  · intro m hm
    simp only [Finset.mem_range] at hm
    refine ⟨⟨2 * m + (i : ℕ) % 2, by omega⟩, ?_, ?_⟩
    · simp only [eqBefore, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨by show 2 * m + (i : ℕ) % 2 < (i : ℕ); omega, ?_⟩
      rw [altSeq_eq_iff]
      show (2 * m + (i : ℕ) % 2) % 2 = (i : ℕ) % 2
      omega
    · show (2 * m + (i : ℕ) % 2) / 2 = m
      omega

lemma card_neqAfter_alt (k : ℕ) (i : Fin (2 * k + 1)) :
    (neqAfter (altSeq (2 * k + 1)) i).card = k - (i : ℕ) / 2 := by
  have h2 : (i : ℕ) % 2 < 2 := Nat.mod_lt _ (by norm_num)
  rw [← Finset.card_range (k - (i : ℕ) / 2)]
  apply Finset.card_bij (fun (j : Fin (2 * k + 1)) _ ↦ ((j : ℕ) - (i : ℕ) - 1) / 2)
  · intro j hj
    simp only [neqAfter, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    have hpar : ¬ ((j : ℕ) % 2 = (i : ℕ) % 2) := altSeq_eq_iff.not.mp hj.2
    have hlt : (i : ℕ) < (j : ℕ) := hj.1
    have hj2 := Nat.mod_lt (j : ℕ) (show 0 < 2 by norm_num)
    simp only [Finset.mem_range]
    omega
  · intro j₁ hj₁ j₂ hj₂ heq
    simp only [neqAfter, Finset.mem_filter, Finset.mem_univ, true_and] at hj₁ hj₂
    have hpar1 : ¬ ((j₁ : ℕ) % 2 = (i : ℕ) % 2) := altSeq_eq_iff.not.mp hj₁.2
    have hpar2 : ¬ ((j₂ : ℕ) % 2 = (i : ℕ) % 2) := altSeq_eq_iff.not.mp hj₂.2
    have hlt1 : (i : ℕ) < (j₁ : ℕ) := hj₁.1
    have hlt2 : (i : ℕ) < (j₂ : ℕ) := hj₂.1
    have hj1m := Nat.mod_lt (j₁ : ℕ) (show 0 < 2 by norm_num)
    have hj2m := Nat.mod_lt (j₂ : ℕ) (show 0 < 2 by norm_num)
    have heq2 : ((j₁ : ℕ) - (i : ℕ) - 1) / 2 = ((j₂ : ℕ) - (i : ℕ) - 1) / 2 := heq
    apply Fin.ext
    omega
  · intro m hm
    simp only [Finset.mem_range] at hm
    refine ⟨⟨(i : ℕ) + 1 + 2 * m, by omega⟩, ?_, ?_⟩
    · simp only [neqAfter, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨by show (i : ℕ) < (i : ℕ) + 1 + 2 * m; omega, ?_⟩
      have hne : ¬ (((i : ℕ) + 1 + 2 * m) % 2 = (i : ℕ) % 2) := by omega
      exact altSeq_eq_iff.not.mpr hne
    · show ((i : ℕ) + 1 + 2 * m - (i : ℕ) - 1) / 2 = m
      omega

lemma f_alt (k : ℕ) (i : Fin (2 * k + 1)) : f (altSeq (2 * k + 1)) i = k := by
  rw [f_apply, card_eqBefore_alt, card_neqAfter_alt]
  have hilt := i.isLt
  omega

/-- The alternating sequence attains the bound. -/
lemma T_alt (k : ℕ) : numGoodTriples (altSeq (2 * k + 1)) = (2 * k + 1) * k.choose 2 := by
  rw [usa1987_p5_part1]
  rw [show (∑ i : Fin (2 * k + 1), (f (altSeq (2 * k + 1)) i).choose 2) =
      ∑ i : Fin (2 * k + 1), k.choose 2 from
    Finset.sum_congr rfl fun i _ ↦ by rw [f_alt]]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

snip end

problem usa1987_p5_part2 (hn : Odd n) :
    IsLeast (Set.range fun a : Fin n → Bool ↦ numGoodTriples a) (minT n) := by
  obtain ⟨k, rfl⟩ := hn
  have hmin : minT (2 * k + 1) = (2 * k + 1) * k.choose 2 := by
    have h8 := key_div k
    unfold minT
    omega
  constructor
  · exact ⟨altSeq (2 * k + 1), by
      show numGoodTriples (altSeq (2 * k + 1)) = minT (2 * k + 1)
      rw [T_alt, hmin]⟩
  · rintro t ⟨a, rfl⟩
    rw [hmin]
    exact lower_bound k a

end Usa1987P5
