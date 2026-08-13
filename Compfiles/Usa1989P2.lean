/-
Copyright (c) 2026 Kimi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics] }

/-!
# USA Mathematical Olympiad 1989, Problem 2

The 20 members of a local tennis club have scheduled exactly 14 two-person
games among themselves, with each member playing in at least one game.
Prove that within this schedule can be found a set of six games with
12 distinct players.
-/

namespace Usa1989P2

open Finset

snip begin

-- We use the "repeat slots" counting argument: the 14 games have 28
-- player-slots. For each member, mark one of the games they play in as
-- their "first" game; this accounts for 20 slots, so at most 8 slots are
-- "repeats", i.e. belong to a member whose game is not that member's
-- first game. At most 8 games contain a repeat slot; discarding those
-- games leaves at least 6 games, and any two of the remaining games are
-- player-disjoint, so they involve 12 distinct players.
--
-- This is Solution 2 of
-- https://math.stackexchange.com/questions/3793869 (USAMO 1989, Problem 2);
-- the same counting argument appears in the kalva/AoPS solutions.

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Every vertex of positive degree is incident to at least one edge. -/
lemma incidenceFinset_nonempty_of_degree_pos (G : SimpleGraph V) [DecidableRel G.Adj]
    {v : V} (hv : 1 ≤ G.degree v) : (G.incidenceFinset v).Nonempty := by
  rw [← Finset.card_pos, SimpleGraph.card_incidenceFinset_eq_degree]
  exact hv

/-- In a finite simple graph with minimum degree at least one, there is a set
of pairwise vertex-disjoint edges of size at least `|V| - |E|`. -/
theorem exists_pairwise_disjoint_edges (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdeg : ∀ v : V, 1 ≤ G.degree v) :
    ∃ s : Finset (Sym2 V), s ⊆ G.edgeFinset ∧
      Fintype.card V - #G.edgeFinset ≤ #s ∧
      ∀ e₁ ∈ s, ∀ e₂ ∈ s, e₁ ≠ e₂ → ∀ v : V, ¬ (v ∈ e₁ ∧ v ∈ e₂) := by
  -- For each vertex choose one "first" incident edge.
  have hne : ∀ v : V, (G.incidenceFinset v).Nonempty :=
    fun v ↦ incidenceFinset_nonempty_of_degree_pos G (hdeg v)
  let first : V → Sym2 V := fun v ↦ (hne v).choose
  have hfirst : ∀ v : V, first v ∈ G.incidenceFinset v := fun v ↦ (hne v).choose_spec
  -- An edge is "bad" if it is incident to some vertex without being that
  -- vertex's first edge.
  set bad : Finset (Sym2 V) :=
    Finset.univ.biUnion (fun v ↦ (G.incidenceFinset v).erase (first v)) with hbad_def
  have hbad_sub : bad ⊆ G.edgeFinset := by
    intro e he
    rw [hbad_def, Finset.mem_biUnion] at he
    obtain ⟨v, -, hv⟩ := he
    exact G.incidenceFinset_subset v (Finset.mem_erase.mp hv).2
  -- Count the bad edges: each vertex contributes at most `degree v - 1` of them.
  have hbad_card : #bad + Fintype.card V ≤ 2 * #G.edgeFinset := by
    have h1 : #bad ≤ ∑ v : V, (G.degree v - 1) := by
      calc #bad ≤ ∑ v : V, #((G.incidenceFinset v).erase (first v)) := by
              rw [hbad_def]
              exact Finset.card_biUnion_le
        _ = ∑ v : V, (G.degree v - 1) :=
              Finset.sum_congr rfl fun v _ ↦ by
                rw [Finset.card_erase_of_mem (hfirst v),
                  SimpleGraph.card_incidenceFinset_eq_degree]
    have h2 : ∑ v : V, (G.degree v - 1) + Fintype.card V = 2 * #G.edgeFinset := by
      have h3 : ∑ v : V, (G.degree v - 1) + Fintype.card V = ∑ v : V, G.degree v := by
        rw [show Fintype.card V = ∑ _v : V, 1 by simp]
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun v _ ↦ Nat.sub_add_cancel (hdeg v)
      rwa [SimpleGraph.sum_degrees_eq_twice_card_edges] at h3
    omega
  -- The surviving edges are pairwise vertex-disjoint.
  refine ⟨G.edgeFinset \ bad, Finset.sdiff_subset, ?_, ?_⟩
  · -- cardinality bound
    rw [Finset.card_sdiff_of_subset hbad_sub]
    omega
  · -- disjointness
    intro e₁ he₁ e₂ he₂ hne12 v ⟨hv1, hv2⟩
    rw [Finset.mem_sdiff] at he₁ he₂
    -- An edge incident to `v` that is not bad must be `v`'s first edge.
    have key : ∀ e : Sym2 V, e ∈ G.edgeFinset → e ∉ bad → v ∈ e → e = first v := by
      intro e heE hebad hve
      have heI : e ∈ G.incidenceFinset v :=
        (G.mem_incidenceFinset v e).mpr ⟨SimpleGraph.mem_edgeFinset.mp heE, hve⟩
      by_contra hne'
      exact hebad (Finset.subset_biUnion_of_mem _ (Finset.mem_univ v)
        (Finset.mem_erase.mpr ⟨hne', heI⟩))
    exact hne12 ((key e₁ he₁.1 he₁.2 hv1).trans (key e₂ he₂.1 he₂.2 hv2).symm)

snip end

problem usa1989_p2
    (G : SimpleGraph (Fin 20)) [DecidableRel G.Adj]
    (hcard : #G.edgeFinset = 14)
    (hdeg : ∀ v : Fin 20, 1 ≤ G.degree v) :
    ∃ s : Finset (Sym2 (Fin 20)), s ⊆ G.edgeFinset ∧ #s = 6 ∧
      #(s.biUnion Sym2.toFinset) = 12 := by
  obtain ⟨s, hsub, hcard', hdisj⟩ := exists_pairwise_disjoint_edges G hdeg
  rw [hcard, Fintype.card_fin] at hcard'
  obtain ⟨t, hts, htc⟩ := Finset.exists_subset_card_eq (show 6 ≤ #s by omega)
  refine ⟨t, hts.trans hsub, htc, ?_⟩
  have hpair : (t : Set (Sym2 (Fin 20))).PairwiseDisjoint Sym2.toFinset := by
    intro e₁ he₁ e₂ he₂ hne
    refine Finset.disjoint_left.mpr fun v hv1 hv2 ↦ ?_
    rw [Sym2.mem_toFinset] at hv1 hv2
    exact hdisj e₁ (hts (Finset.mem_coe.mp he₁)) e₂ (hts (Finset.mem_coe.mp he₂)) hne v
      ⟨hv1, hv2⟩
  rw [Finset.card_biUnion hpair]
  trans ∑ _e ∈ t, 2
  · exact Finset.sum_congr rfl fun e he ↦
      Sym2.card_toFinset_of_not_isDiag e
        (SimpleGraph.not_isDiag_of_mem_edgeFinset (hsub (hts he)))
  · simp [htc]

end Usa1989P2
