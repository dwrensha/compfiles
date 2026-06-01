/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Batteries.Data.List.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.Chain
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Tactic.Linarith

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
USA Mathematical Olympiad 1999, Problem 1

Some checkers placed on an n × n checkerboard satisfy the following conditions:
 a. every square that does not contain a checker shares a side with one that does;
 b. given any pair of squares that contain checkers, there is a sequence of squares
    containing checkers, starting and ending with the given squares, such that
    every two consecutive squares of the sequence share a side.

Prove that at least (n²-2)/3 checkers have been placed on the board.
-/

namespace Usa1999P1

def checkerboard (n : ℕ) := Fin n × Fin n

def adjacent {n : ℕ} : checkerboard n → checkerboard n → Prop
| ⟨a1, a2⟩, ⟨b1, b2⟩ =>
  (a1.val = b1.val ∧ a2.val = b2.val + 1) ∨
  (a1.val = b1.val ∧ a2.val + 1 = b2.val) ∨
  (a2.val = b2.val ∧ a1.val = b1.val + 1) ∨
  (a2.val = b2.val ∧ a1.val + 1 = b1.val )

snip begin

instance checkerboardFintype (n : ℕ) : Fintype (checkerboard n) :=
  inferInstanceAs (Fintype (Fin n × Fin n))

instance checkerboardDecidableEq (n : ℕ) : DecidableEq (checkerboard n) :=
  inferInstanceAs (DecidableEq (Fin n × Fin n))

instance pathGraphDecidableRel (n : ℕ) : DecidableRel (SimpleGraph.pathGraph n).Adj := by
  intro x y
  rw [SimpleGraph.pathGraph_adj]
  infer_instance

instance adjacentDecidableRel (n : ℕ) : DecidableRel (@adjacent n) := by
  intro x y
  rcases x with ⟨x1, x2⟩
  rcases y with ⟨y1, y2⟩
  unfold adjacent
  infer_instance

-- Use the full grid graph and the subgraph induced by the checkers.
def gridGraph (n : ℕ) : SimpleGraph (checkerboard n) :=
  SimpleGraph.pathGraph n □ SimpleGraph.pathGraph n

lemma gridGraph_adj {n : ℕ} {x y : checkerboard n} :
    (gridGraph n).Adj x y ↔ adjacent x y := by
  rcases x with ⟨x1, x2⟩
  rcases y with ⟨y1, y2⟩
  simp only [gridGraph, SimpleGraph.boxProd_adj, SimpleGraph.pathGraph_adj, adjacent,
    Fin.ext_iff]
  tauto

instance gridGraphDecidableRel (n : ℕ) : DecidableRel (gridGraph n).Adj := by
  intro x y
  exact decidable_of_iff (adjacent x y) gridGraph_adj.symm

instance gridGraphNeighborSetFintype (n : ℕ) (x : checkerboard n) :
    Fintype ((gridGraph n).neighborSet x) := by
  rcases x with ⟨x1, x2⟩
  unfold gridGraph
  exact SimpleGraph.boxProdFintypeNeighborSet (G := SimpleGraph.pathGraph n)
    (H := SimpleGraph.pathGraph n) (x1, x2)

def checkerGraph {n : ℕ} (c : Finset (checkerboard n)) : SimpleGraph c :=
  (gridGraph n).induce (↑c : Set (checkerboard n))

instance checkerGraphDecidableRel {n : ℕ} (c : Finset (checkerboard n)) :
    DecidableRel (checkerGraph c).Adj := by
  unfold checkerGraph
  infer_instance

-- A path vertex has at most one neighbor on each side.
lemma pathGraph_degree_le_two {n : ℕ} (x : Fin n) :
    (SimpleGraph.pathGraph n).degree x ≤ 2 := by
  let side : (SimpleGraph.pathGraph n).neighborSet x → Bool :=
    fun y => decide (y.1.val + 1 = x.val)
  rw [← SimpleGraph.card_neighborSet_eq_degree]
  refine (Fintype.card_le_of_injective side ?_).trans_eq Fintype.card_bool
  intro y z hyz
  apply Subtype.ext
  apply Fin.ext
  have hy := SimpleGraph.pathGraph_adj.mp y.2
  have hz := SimpleGraph.pathGraph_adj.mp z.2
  by_cases hy' : y.1.val + 1 = x.val <;>
    by_cases hz' : z.1.val + 1 = x.val
  · exact Nat.add_right_cancel (hy'.trans hz'.symm)
  · simp [side, hy', hz'] at hyz
  · simp [side, hy', hz'] at hyz
  · exact (hy.resolve_right hy').symm.trans (hz.resolve_right hz')

-- A square has at most four side-neighbors.
lemma gridGraph_degree_le_four {n : ℕ} (x : checkerboard n) :
    (gridGraph n).degree x ≤ 4 := by
  change (SimpleGraph.pathGraph n □ SimpleGraph.pathGraph n).degree x ≤ 4
  rw [SimpleGraph.degree_boxProd]
  exact Nat.add_le_add (pathGraph_degree_le_two x.1) (pathGraph_degree_le_two x.2)

-- The path hypothesis makes the checker graph preconnected.
lemma checkerGraph_preconnected {n : ℕ} {c : Finset (checkerboard n)}
    (hb : ∀ x ∈ c, ∀ y ∈ c,
      ∃ p : List (checkerboard n),
        (∀ z, z ∈ p → z ∈ c) ∧
        List.IsChain adjacent p ∧
        List.head? p = x ∧
        List.getLast? p = y) :
    (checkerGraph c).Preconnected := by
  intro x y
  obtain ⟨p, hp, hchain, hhead, hlast⟩ := hb x.1 x.2 y.1 y.2
  have hpne : p ≠ [] := by
    rintro rfl
    simp at hhead
  let q : List c := p.pmap (fun z hz ↦ ⟨z, hz⟩) hp
  have hqne : q ≠ [] := by simpa [q] using hpne
  have hqchain : q.IsChain (checkerGraph c).Adj :=
    List.isChain_pmap_of_isChain
      (fun a b ha hb hab ↦ by simpa [checkerGraph] using gridGraph_adj.mpr hab) hchain hp
  have hreach := (SimpleGraph.Walk.ofSupport q hqne hqchain).reachable
  have hphead : p.head hpne = x.1 := by
    have := List.head?_eq_some_head hpne
    rw [hhead] at this
    exact Option.some.inj this.symm
  have hplast : p.getLast hpne = y.1 := by
    have := List.getLast?_eq_some_getLast hpne
    rw [hlast] at this
    exact Option.some.inj this.symm
  convert hreach using 1 <;> apply Subtype.ext <;> simp [q, hphead, hplast]

-- A preconnected finite graph has internal degree sum at least twice its vertex count minus two.
lemma preconnected_twice_card_le_sum_degrees_add_two
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Preconnected) :
    2 * Fintype.card V ≤ (∑ v, G.degree v) + 2 := by
  cases isEmpty_or_nonempty V with
  | inl hV =>
      letI := hV
      simp
  | inr hV =>
      letI := hV
      have h := (show G.Connected from ⟨hG⟩).card_vert_le_card_edgeSet_add_one
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet] at h
      rw [SimpleGraph.sum_degrees_eq_twice_card_edges]
      linarith

def emptySquares {n : ℕ} (c : Finset (checkerboard n)) :
    Finset (checkerboard n) :=
  Finset.univ \ c

def boundaryNeighbors {n : ℕ} (c : Finset (checkerboard n)) (x : c) :
    Finset (checkerboard n) :=
  (gridGraph n).neighborFinset x.1 \ c

-- Count checker-neighbors inside the full grid neighborhood.
lemma checkerGraph_degree_eq_inter {n : ℕ} (c : Finset (checkerboard n)) (x : c) :
    (checkerGraph c).degree x =
      ((gridGraph n).neighborFinset x.1 ∩ c).card := by
  let emb : c ↪ checkerboard n := ⟨Subtype.val, Subtype.val_injective⟩
  have hmap : ((checkerGraph c).neighborFinset x).map emb =
      (gridGraph n).neighborFinset x.1 ∩ c := by
    ext y
    simp [emb, SimpleGraph.mem_neighborFinset, checkerGraph]
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  rw [← hmap, Finset.card_map]

-- Split each checker degree into internal and boundary neighbors.
lemma gridGraph_degree_eq_checkerGraph_degree_add_boundary {n : ℕ}
    (c : Finset (checkerboard n)) (x : c) :
    (gridGraph n).degree x.1 = (checkerGraph c).degree x +
      (boundaryNeighbors c x).card := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, checkerGraph_degree_eq_inter,
    boundaryNeighbors]
  exact (Finset.card_inter_add_card_sdiff _ _).symm

-- Every empty square is covered by a boundary-neighbor set of some checker.
lemma emptySquares_card_le_boundary_sum {n : ℕ} (c : Finset (checkerboard n))
    (ha : ∀ x : checkerboard n, x ∈ c ∨ (∃ y ∈ c, adjacent x y)) :
    (emptySquares c).card ≤ ∑ x : c, (boundaryNeighbors c x).card := by
  have hcover : emptySquares c ⊆
      (Finset.univ : Finset c).biUnion (boundaryNeighbors c) := by
    intro z hz
    have hz_not : z ∉ c := by
      simpa [emptySquares] using hz
    rcases ha z with hzc | ⟨y, hyc, hzy⟩
    · exact False.elim (hz_not hzc)
    · refine Finset.mem_biUnion.mpr ⟨⟨y, hyc⟩, Finset.mem_univ _, ?_⟩
      rw [boundaryNeighbors, Finset.mem_sdiff, SimpleGraph.mem_neighborFinset]
      exact ⟨(gridGraph_adj.mpr hzy).symm, hz_not⟩
  calc
    (emptySquares c).card ≤
        ((Finset.univ : Finset c).biUnion (boundaryNeighbors c)).card :=
      Finset.card_le_card hcover
    _ ≤ ∑ x : c, (boundaryNeighbors c x).card := by
      simpa using
        (Finset.card_biUnion_le
          (s := (Finset.univ : Finset c)) (t := boundaryNeighbors c))

-- Empty squares and checker squares partition the board.
lemma emptySquares_card_add_checker_card {n : ℕ} (c : Finset (checkerboard n)) :
    (emptySquares c).card + c.card = n^2 := by
  rw [emptySquares]
  rw [Finset.card_sdiff_add_card_eq_card (s := c)
    (t := (Finset.univ : Finset (checkerboard n))) (by simp)]
  rw [Finset.card_univ]
  change Fintype.card (Fin n × Fin n) = n ^ 2
  rw [Fintype.card_prod, Fintype.card_fin, pow_two]

snip end

problem usa1999_p1 (n : ℕ) (c : Finset (checkerboard n))
    (ha : ∀ x : checkerboard n, x ∈ c ∨ (∃ y ∈ c, adjacent x y))
    (hb : ∀ x ∈ c, ∀ y ∈ c,
      ∃ p : List (checkerboard n),
        (∀ z, z ∈ p → z ∈ c) ∧
        List.IsChain adjacent p ∧
        List.head? p = x ∧
        List.getLast? p = y) :
    n^2 ≤ c.card * 3 + 2 := by
  let U := emptySquares c
  let B := ∑ x : c, (boundaryNeighbors c x).card
  -- Empty squares are charged to checker-empty boundary incidences.
  have hU_le_B : U.card ≤ B := by
    simpa [U, B] using emptySquares_card_le_boundary_sum c ha
  have hU_add : U.card + c.card = n^2 := by
    simpa [U] using emptySquares_card_add_checker_card c
  -- Sum degrees in the full grid over checker squares.
  have htotal_degrees_le : ∑ x : c, (gridGraph n).degree x.1 ≤ 4 * c.card := by
    calc
      ∑ x : c, (gridGraph n).degree x.1 ≤ ∑ _x : c, 4 := by
        apply Finset.sum_le_sum
        intro x _
        exact gridGraph_degree_le_four x.1
      _ = 4 * c.card := by
        simp [Nat.mul_comm]
  have hconnected :
      2 * c.card ≤ (∑ x : c, (checkerGraph c).degree x) + 2 := by
    simpa [Fintype.card_coe] using
      preconnected_twice_card_le_sum_degrees_add_two (checkerGraph c)
        (checkerGraph_preconnected hb)
  have hsum_partition :
      ∑ x : c, (gridGraph n).degree x.1 =
        ∑ x : c, (checkerGraph c).degree x + B := by
    simp_rw [gridGraph_degree_eq_checkerGraph_degree_add_boundary]
    rw [Finset.sum_add_distrib]
  linarith


end Usa1999P1
