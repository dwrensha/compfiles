/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Ring.Canonical
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Ring
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics] }

/-!
# USA Mathematical Olympiad 1985, Problem 4

A graph has n > 2 points. Show that we can find two points A and B such that
at least ⌊n/2⌋ - 1 of the remaining points are joined to either both or
neither of A and B.
-/

namespace Usa1985P4

open Finset

snip begin

/-- `mixedRel n G X p` says that the vertex `X` is distinct from the two endpoints
of the pair `p` and is adjacent to exactly one of them. -/
def mixedRel (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (X : Fin n)
    (p : Fin n × Fin n) : Prop :=
  X ≠ p.1 ∧ X ≠ p.2 ∧ ((G.Adj X p.1 ∧ ¬ G.Adj X p.2) ∨ (¬ G.Adj X p.1 ∧ G.Adj X p.2))

instance (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (X : Fin n)
    (p : Fin n × Fin n) : Decidable (mixedRel n G X p) := by
  unfold mixedRel
  infer_instance

/-- The "bad" vertices for a pair `p`: the remaining vertices that are joined
to exactly one of the two endpoints of `p`. -/
def badPair (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (p : Fin n × Fin n) :
    Finset (Fin n) :=
  Finset.univ.filter fun X => mixedRel n G X p

lemma badPair_eq_bipartiteBelow (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (p : Fin n × Fin n) :
    badPair n G p = Finset.univ.bipartiteBelow (mixedRel n G) p := rfl

/-- The neighbourhood of `X` does not contain `X`. -/
lemma neighborFinset_subset_erase (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (X : Fin n) : G.neighborFinset X ⊆ Finset.univ.erase X := by
  intro Z hZ
  rw [SimpleGraph.mem_neighborFinset] at hZ
  exact Finset.mem_erase.mpr ⟨(SimpleGraph.Adj.ne hZ).symm, Finset.mem_univ Z⟩

/-- The degree of a vertex is at most `n - 1`. -/
lemma degree_le (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (X : Fin n) :
    G.degree X ≤ n - 1 := by
  have h := Finset.card_le_card (neighborFinset_subset_erase n G X)
  rw [Finset.card_erase_of_mem (Finset.mem_univ X), Finset.card_univ, Fintype.card_fin,
    SimpleGraph.card_neighborFinset_eq_degree] at h
  exact h

/-- For a fixed vertex `X`, the number of ordered pairs `(Y, Z)` with `Y ≠ Z` such that
`X` is joined to exactly one of `Y` and `Z` equals `2 * (d * (n - 1 - d))`, where
`d = G.degree X`: choose which endpoint is adjacent to `X`, then choose that endpoint
(a neighbour of `X`) and the other one (a non-neighbour different from `X`). -/
lemma fiber_card (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (X : Fin n) :
    ((Finset.offDiag Finset.univ).bipartiteAbove (mixedRel n G) X).card =
      2 * (G.degree X * (n - 1 - G.degree X)) := by
  -- The two distinctness conditions in `mixedRel` are (partially) redundant.
  have key : ∀ p : Fin n × Fin n, mixedRel n G X p ↔
      (X ≠ p.2 ∧ G.Adj X p.1 ∧ ¬ G.Adj X p.2) ∨ (X ≠ p.1 ∧ ¬ G.Adj X p.1 ∧ G.Adj X p.2) := by
    rintro ⟨Y, Z⟩
    show (X ≠ Y ∧ X ≠ Z ∧ ((G.Adj X Y ∧ ¬ G.Adj X Z) ∨ (¬ G.Adj X Y ∧ G.Adj X Z))) ↔
      ((X ≠ Z ∧ G.Adj X Y ∧ ¬ G.Adj X Z) ∨ (X ≠ Y ∧ ¬ G.Adj X Y ∧ G.Adj X Z))
    constructor
    · rintro ⟨hXY, hXZ, h | h⟩
      · exact Or.inl ⟨hXZ, h⟩
      · exact Or.inr ⟨hXY, h⟩
    · rintro (⟨hXZ, hA, hB⟩ | ⟨hXY, hA, hB⟩)
      · exact ⟨SimpleGraph.Adj.ne hA, hXZ, Or.inl ⟨hA, hB⟩⟩
      · exact ⟨hXY, SimpleGraph.Adj.ne hB, Or.inr ⟨hA, hB⟩⟩
  -- Split the fiber into the two orientations (which endpoint is adjacent to `X`).
  have hunion : (Finset.offDiag Finset.univ).bipartiteAbove (mixedRel n G) X =
      (Finset.offDiag Finset.univ).filter (fun p => X ≠ p.2 ∧ G.Adj X p.1 ∧ ¬ G.Adj X p.2) ∪
        (Finset.offDiag Finset.univ).filter
          (fun p => X ≠ p.1 ∧ ¬ G.Adj X p.1 ∧ G.Adj X p.2) := by
    rw [show (Finset.offDiag Finset.univ).bipartiteAbove (mixedRel n G) X =
          (Finset.offDiag Finset.univ).filter (fun p => mixedRel n G X p) from rfl,
      Finset.filter_congr (fun p _ => key p), Finset.filter_or]
  -- Each orientation is a rectangle: neighbours of `X` times non-neighbours of `X`.
  have hrect1 :
      (Finset.offDiag Finset.univ).filter (fun p => X ≠ p.2 ∧ G.Adj X p.1 ∧ ¬ G.Adj X p.2) =
        (G.neighborFinset X) ×ˢ ((Finset.univ.erase X).filter fun Z => ¬ G.Adj X Z) := by
    ext ⟨Y, Z⟩
    simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_univ, true_and,
      Finset.mem_product, SimpleGraph.mem_neighborFinset, Finset.mem_erase, and_true]
    constructor
    · rintro ⟨hYZ, hXZ, hA, hB⟩
      exact ⟨hA, hXZ.symm, hB⟩
    · rintro ⟨hA, hXZ, hB⟩
      exact ⟨(fun hYZ => hB (hYZ ▸ hA)), hXZ.symm, hA, hB⟩
  have hrect2 :
      (Finset.offDiag Finset.univ).filter (fun p => X ≠ p.1 ∧ ¬ G.Adj X p.1 ∧ G.Adj X p.2) =
        ((Finset.univ.erase X).filter fun Z => ¬ G.Adj X Z) ×ˢ (G.neighborFinset X) := by
    ext ⟨Y, Z⟩
    simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_univ, true_and,
      Finset.mem_product, SimpleGraph.mem_neighborFinset, Finset.mem_erase, and_true]
    constructor
    · rintro ⟨hYZ, hXY, hA, hB⟩
      exact ⟨⟨hXY.symm, hA⟩, hB⟩
    · rintro ⟨⟨hXY, hA⟩, hB⟩
      exact ⟨(fun hYZ => hA (hYZ.symm ▸ hB)), hXY.symm, hA, hB⟩
  -- The two rectangles are disjoint.
  have hdisj : Disjoint
      ((Finset.offDiag Finset.univ).filter (fun p => X ≠ p.2 ∧ G.Adj X p.1 ∧ ¬ G.Adj X p.2))
      ((Finset.offDiag Finset.univ).filter
        (fun p => X ≠ p.1 ∧ ¬ G.Adj X p.1 ∧ G.Adj X p.2)) := by
    rw [hrect1, hrect2, Finset.disjoint_left]
    rintro ⟨Y, Z⟩ h1 h2
    simp only [Finset.mem_product, SimpleGraph.mem_neighborFinset, Finset.mem_filter,
      Finset.mem_erase, Finset.mem_univ, and_true] at h1 h2
    exact h2.1.2 h1.1
  -- The number of non-neighbours of `X` (other than `X` itself) is `n - 1 - d`.
  have hM : ((Finset.univ.erase X).filter fun Z => ¬ G.Adj X Z).card =
      n - 1 - G.degree X := by
    have hMeq : ((Finset.univ.erase X).filter fun Z => ¬ G.Adj X Z) =
        (Finset.univ.erase X) \ G.neighborFinset X := by
      ext Z
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true,
        Finset.mem_sdiff, SimpleGraph.mem_neighborFinset]
    rw [hMeq, Finset.card_sdiff_of_subset (neighborFinset_subset_erase n G X),
      Finset.card_erase_of_mem (Finset.mem_univ X), Finset.card_univ, Fintype.card_fin,
      SimpleGraph.card_neighborFinset_eq_degree]
  rw [hunion, Finset.card_union_of_disjoint hdisj, hrect1, hrect2, Finset.card_product,
    Finset.card_product, hM, SimpleGraph.card_neighborFinset_eq_degree]
  ring

/-- Double counting: summing the number of bad vertices over all ordered pairs
`(Y, Z)` with `Y ≠ Z` equals the sum over vertices `X` of `2 * (d_X * (n - 1 - d_X))`. -/
lemma double_count (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (∑ p ∈ Finset.offDiag (Finset.univ : Finset (Fin n)), (badPair n G p).card) =
      ∑ X : Fin n, 2 * (G.degree X * (n - 1 - G.degree X)) := by
  calc (∑ p ∈ Finset.offDiag (Finset.univ : Finset (Fin n)), (badPair n G p).card)
      = ∑ X : Fin n, ((Finset.offDiag Finset.univ).bipartiteAbove (mixedRel n G) X).card := by
        simp only [badPair_eq_bipartiteBelow]
        exact (Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
          (s := (Finset.univ : Finset (Fin n))) (t := Finset.offDiag Finset.univ)
          (r := mixedRel n G)).symm
    _ = ∑ X : Fin n, 2 * (G.degree X * (n - 1 - G.degree X)) :=
        Finset.sum_congr rfl fun X _ => fiber_card n G X

/-- Twice the total number of bad incidences is at most `n * (n - 1)^2`, since for each
vertex `X` of degree `d` we have `4 * d * (n - 1 - d) ≤ (n - 1)^2` (AM-GM). -/
lemma two_mul_sum_badPair_le (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    2 * (∑ p ∈ Finset.offDiag (Finset.univ : Finset (Fin n)), (badPair n G p).card) ≤
      n * (n - 1)^2 := by
  rw [double_count, Finset.mul_sum]
  calc (∑ X : Fin n, 2 * (2 * (G.degree X * (n - 1 - G.degree X))))
      ≤ ∑ _X : Fin n, (n - 1)^2 := by
        apply Finset.sum_le_sum
        intro X _
        have hd : G.degree X ≤ n - 1 := degree_le n G X
        have h := four_mul_le_sq_add (G.degree X) (n - 1 - G.degree X)
        rw [Nat.add_sub_cancel' hd] at h
        have e : 2 * (2 * (G.degree X * (n - 1 - G.degree X))) =
            4 * G.degree X * (n - 1 - G.degree X) := by ring
        rw [e]
        exact h
    _ = n * (n - 1)^2 := by
        simp

/-- Averaging: some ordered pair `(A, B)` with `A ≠ B` has at most `⌊(n - 1)/2⌋`
bad remaining vertices. -/
lemma exists_pair_le (n : ℕ) (hn : 2 < n) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    ∃ p ∈ Finset.offDiag (Finset.univ : Finset (Fin n)),
      (badPair n G p).card ≤ (n - 1) / 2 := by
  by_contra h
  push Not at h
  have h3 : (∑ p ∈ Finset.offDiag (Finset.univ : Finset (Fin n)), ((n - 1)/2 + 1)) ≤
      ∑ p ∈ Finset.offDiag (Finset.univ : Finset (Fin n)), (badPair n G p).card :=
    Finset.sum_le_sum fun p hp => Nat.succ_le_iff.mpr (h p hp)
  simp only [Finset.sum_const, Finset.offDiag_card, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at h3
  norm_cast at h3
  -- The average would exceed `n * (n - 1)^2`, contradicting `two_mul_sum_badPair_le`.
  have key : n * (n - 1)^2 < 2 * ((n * n - n) * ((n - 1)/2 + 1)) := by
    have hpos : 0 < n * n - n := by
      have h1 : (0 : ℕ) < n := by lia
      have h2 : (0 : ℕ) < n - 1 := by lia
      have hm := Nat.mul_pos h1 h2
      have h4 : n * (n - 1) = n * n - n := by rw [mul_tsub, mul_one]
      rwa [h4] at hm
    have e1 : n * (n - 1)^2 = (n * n - n) * (n - 1) := by
      have h4 : n * (n - 1) = n * n - n := by rw [mul_tsub, mul_one]
      rw [pow_two, ← mul_assoc, h4]
    have e2 : 2 * ((n * n - n) * ((n - 1)/2 + 1)) =
        (n * n - n) * (2 * ((n - 1)/2 + 1)) := by ring
    rw [e1, e2]
    exact Nat.mul_lt_mul_of_pos_left (by lia) hpos
  have chain : 2 * ((n * n - n) * ((n - 1)/2 + 1)) ≤ n * (n - 1)^2 :=
    le_trans (by gcongr) (two_mul_sum_badPair_le n G)
  exact absurd chain (not_le_of_gt key)

/-- The vertices joined to both or neither endpoint of `p` are the remaining vertices
that are not bad; there are `(n - 2) - (#bad)` of them. -/
lemma answer_card (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (p : Fin n × Fin n)
    (hp : p ∈ Finset.offDiag (Finset.univ : Finset (Fin n))) :
    (Finset.univ.filter fun X => X ≠ p.1 ∧ X ≠ p.2 ∧ (G.Adj X p.1 ↔ G.Adj X p.2)).card =
      (n - 2) - (badPair n G p).card := by
  have hsplit :
      (Finset.univ.filter fun X => X ≠ p.1 ∧ X ≠ p.2 ∧ (G.Adj X p.1 ↔ G.Adj X p.2)) =
        (Finset.univ.filter fun X => X ≠ p.1 ∧ X ≠ p.2) \ badPair n G p := by
    ext X
    simp only [badPair, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
    rw [mixedRel]
    tauto
  have hsub : badPair n G p ⊆ Finset.univ.filter (fun X => X ≠ p.1 ∧ X ≠ p.2) := by
    intro X hX
    simp only [badPair, Finset.mem_filter, Finset.mem_univ, true_and] at hX ⊢
    rw [mixedRel] at hX
    exact ⟨hX.1, hX.2.1⟩
  have hcard : (Finset.univ.filter fun X : Fin n => X ≠ p.1 ∧ X ≠ p.2).card = n - 2 := by
    have hne : p.1 ≠ p.2 := (Finset.mem_offDiag.mp hp).2.2
    have hset : (Finset.univ.filter fun X : Fin n => X ≠ p.1 ∧ X ≠ p.2) =
        (Finset.univ.erase p.1).erase p.2 := by
      ext X
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, and_true]
      tauto
    have hmem : p.2 ∈ Finset.univ.erase p.1 :=
      Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ _⟩
    rw [hset, Finset.card_erase_of_mem hmem, Finset.card_erase_of_mem (Finset.mem_univ p.1),
      Finset.card_univ, Fintype.card_fin]
    lia
  rw [hsplit, Finset.card_sdiff_of_subset hsub, hcard]

snip end

problem usa1985_p4 (n : ℕ) (hn : 2 < n) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    ∃ A B : Fin n, A ≠ B ∧
      n / 2 - 1 ≤ (Finset.univ.filter fun X =>
        X ≠ A ∧ X ≠ B ∧ (G.Adj X A ↔ G.Adj X B)).card := by
  obtain ⟨p, hp, hple⟩ := exists_pair_le n hn G
  refine ⟨p.1, p.2, (Finset.mem_offDiag.mp hp).2.2, ?_⟩
  rw [answer_card n G p hp]
  lia

end Usa1985P4
