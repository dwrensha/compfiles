/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Tactic.NormNum
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics] }

/-!
# USA Mathematical Olympiad 1982, Problem 1

A graph has 1982 points. Given any four points, there is at least one
joined to the other three. What is the smallest number of points which
are joined to 1981 points?
-/

namespace Usa1982P1

open Classical

/-- The hypothesis of the problem: among any four vertices of the graph,
some vertex is adjacent to the other three. -/
def FourPointProperty (G : SimpleGraph (Fin 1982)) : Prop :=
  ∀ s : Finset (Fin 1982), s.card = 4 → ∃ v ∈ s, ∀ w ∈ s, w ≠ v → G.Adj v w

/-- A vertex is *universal* if it is joined to all 1981 other vertices. -/
def IsUniversal (G : SimpleGraph (Fin 1982)) (v : Fin 1982) : Prop :=
  ∀ w, w ≠ v → G.Adj v w

determine solution : ℕ := 1979

snip begin

/-- A finset of four distinct vertices has cardinality four. -/
lemma card_four_of_distinct {a b c d : Fin 1982} (hab : a ≠ b) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    ({a, b, c, d} : Finset (Fin 1982)).card = 4 := by
  rw [Finset.card_insert_of_notMem (by simp [hab, hac, had]),
      Finset.card_insert_of_notMem (by simp [hbc, hbd]),
      Finset.card_insert_of_notMem (by simp [hcd]),
      Finset.card_singleton]

/-- Lower bound: in any graph satisfying `FourPointProperty`, at most three
vertices fail to be universal, so at least 1979 vertices are universal.

The proof follows the official solution. Suppose four vertices were not
universal. Let `A` be one of them and let `B` be a vertex not joined to `A`.
Then any two other vertices `X, Y` must be joined (else no vertex of
`{A, B, X, Y}` would be joined to the other three). Take two further
non-universal vertices `C, D ∉ {A, B}`. Each of `C, D` is joined to every
vertex except possibly `A` and `B`, and being non-universal it must miss one
of those. But then no vertex of `{A, B, C, D}` is joined to the other three,
a contradiction. -/
lemma card_universal_ge (G : SimpleGraph (Fin 1982)) (hG : FourPointProperty G) :
    1979 ≤ (Finset.univ.filter (IsUniversal G)).card := by
  set NU := Finset.univ.filter (fun v => ¬ IsUniversal G v) with hNU
  have hpartition : (Finset.univ.filter (IsUniversal G)).card + NU.card = 1982 := by
    have h := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin 1982))) (p := IsUniversal G)
    rw [Finset.card_univ, Fintype.card_fin] at h
    exact h
  suffices h : NU.card ≤ 3 by omega
  by_contra hcon
  push Not at hcon
  -- Pick a non-universal vertex `A` and a vertex `B` not joined to `A`.
  obtain ⟨A, hA⟩ := Finset.card_pos.mp (show 0 < NU.card by omega)
  have hA' : ¬ IsUniversal G A := (Finset.mem_filter.mp hA).2
  obtain ⟨B, hBA, hAB⟩ : ∃ w, w ≠ A ∧ ¬ G.Adj A w := by
    by_contra hB
    push Not at hB
    exact hA' hB
  -- Any two vertices `X, Y` outside `{A, B}` must be joined.
  have claim : ∀ X Y : Fin 1982, X ≠ Y → X ≠ A → X ≠ B → Y ≠ A → Y ≠ B →
      G.Adj X Y := by
    intro X Y hXY hXA hXB hYA hYB
    have hcard4 : ({A, B, X, Y} : Finset (Fin 1982)).card = 4 :=
      card_four_of_distinct hBA.symm hXA.symm hYA.symm hXB.symm hYB.symm hXY
    obtain ⟨v, hv, hadj⟩ := hG _ hcard4
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact absurd (hadj B (by simp) hBA) hAB
    · exact absurd (hadj A (by simp) hBA.symm).symm hAB
    · exact hadj Y (by simp) hXY.symm
    · exact (hadj X (by simp) hXY).symm
  -- Two more non-universal vertices `C, D` lie outside `{A, B}`.
  have hAerase : (NU.erase A).card = NU.card - 1 := Finset.card_erase_of_mem hA
  have hCD2 : 1 < ((NU.erase A).erase B).card := by
    by_cases hB : B ∈ NU.erase A
    · have hBe := Finset.card_erase_of_mem hB
      omega
    · have hBe : ((NU.erase A).erase B).card = (NU.erase A).card := by
        rw [Finset.erase_eq_of_notMem hB]
      omega
  obtain ⟨C, hC, D, hD, hCD⟩ := Finset.one_lt_card.mp hCD2
  obtain ⟨hCB, hC⟩ := Finset.mem_erase.mp hC
  obtain ⟨hCA, hC⟩ := Finset.mem_erase.mp hC
  obtain ⟨hDB, hD⟩ := Finset.mem_erase.mp hD
  obtain ⟨hDA, hD⟩ := Finset.mem_erase.mp hD
  have hCNU : ¬ IsUniversal G C := (Finset.mem_filter.mp hC).2
  have hDNU : ¬ IsUniversal G D := (Finset.mem_filter.mp hD).2
  -- `C` misses a vertex; by the claim that vertex must be `A` or `B`.
  obtain ⟨wC, hwCne, hwCadj⟩ : ∃ w, w ≠ C ∧ ¬ G.Adj C w := by
    by_contra h
    push Not at h
    exact hCNU h
  have hwCAB : wC = A ∨ wC = B := by
    by_contra h
    push Not at h
    exact hwCadj (claim C wC hwCne.symm hCA hCB h.1 h.2)
  have hCbad : ¬ G.Adj C A ∨ ¬ G.Adj C B := by
    rcases hwCAB with rfl | rfl
    · exact Or.inl hwCadj
    · exact Or.inr hwCadj
  -- Same for `D`.
  obtain ⟨wD, hwDne, hwDadj⟩ : ∃ w, w ≠ D ∧ ¬ G.Adj D w := by
    by_contra h
    push Not at h
    exact hDNU h
  have hwDAB : wD = A ∨ wD = B := by
    by_contra h
    push Not at h
    exact hwDadj (claim D wD hwDne.symm hDA hDB h.1 h.2)
  have hDbad : ¬ G.Adj D A ∨ ¬ G.Adj D B := by
    rcases hwDAB with rfl | rfl
    · exact Or.inl hwDadj
    · exact Or.inr hwDadj
  -- But then no vertex of `{A, B, C, D}` is joined to the other three.
  have hcard4 : ({A, B, C, D} : Finset (Fin 1982)).card = 4 :=
    card_four_of_distinct hBA.symm hCA.symm hDA.symm hCB.symm hDB.symm hCD
  obtain ⟨v, hv, hadj⟩ := hG _ hcard4
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl | rfl
  · exact absurd (hadj B (by simp) hBA) hAB
  · exact absurd (hadj A (by simp) hBA.symm).symm hAB
  · rcases hCbad with h1 | h1
    · exact h1 (hadj A (by simp) hCA.symm)
    · exact h1 (hadj B (by simp) hCB.symm)
  · rcases hDbad with h1 | h1
    · exact h1 (hadj A (by simp) hDA.symm)
    · exact h1 (hadj B (by simp) hDB.symm)

/-- The finset `{0, 1, 2}` of vertices has three elements. -/
lemma card_three : ({0, 1, 2} : Finset (Fin 1982)).card = 3 := by decide

/-- Adjacency in the extremal graph: all pairs of distinct vertices except
`0—1` and `0—2`. -/
def extremalAdj (i j : Fin 1982) : Prop :=
  i ≠ j ∧ ¬ ((i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨ (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0))

/-- The extremal graph: the complete graph on `Fin 1982` with the two edges
`0—1` and `0—2` removed. -/
def extremalGraph : SimpleGraph (Fin 1982) where
  Adj := extremalAdj
  symm := ⟨fun i j h => ⟨h.1.symm, fun hP => h.2 (by tauto)⟩⟩
  loopless := ⟨fun i h => h.1 rfl⟩

/-- In the extremal graph, the universal vertices are exactly those outside
`{0, 1, 2}`. -/
lemma extremal_universal_iff (v : Fin 1982) :
    IsUniversal extremalGraph v ↔ v ≠ 0 ∧ v ≠ 1 ∧ v ≠ 2 := by
  constructor
  · intro h
    by_contra hcon
    have hv : v = 0 ∨ v = 1 ∨ v = 2 := by tauto
    rcases hv with rfl | rfl | rfl
    · have hn : ¬ extremalAdj (0 : Fin 1982) 1 := fun hh => hh.2 (Or.inl ⟨rfl, rfl⟩)
      exact hn (h 1 (by decide))
    · have hn : ¬ extremalAdj (1 : Fin 1982) 0 :=
        fun hh => hh.2 (Or.inr (Or.inl ⟨rfl, rfl⟩))
      exact hn (h 0 (by decide))
    · have hn : ¬ extremalAdj (2 : Fin 1982) 0 :=
        fun hh => hh.2 (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))
      exact hn (h 0 (by decide))
  · rintro ⟨h0, h1, h2⟩ w hwv
    show extremalAdj v w
    refine ⟨hwv.symm, ?_⟩
    rintro (⟨hv0, -⟩ | ⟨hv1, -⟩ | ⟨hv0, -⟩ | ⟨hv2, -⟩)
    · exact h0 hv0
    · exact h1 hv1
    · exact h0 hv0
    · exact h2 hv2

/-- The extremal graph satisfies the four-point condition: any four vertices
contain one outside `{0, 1, 2}`, and that vertex is joined to all others. -/
lemma extremal_fourPoint : FourPointProperty extremalGraph := by
  intro s hs
  obtain ⟨v, hv, hvnot⟩ : ∃ v ∈ s, v ∉ ({0, 1, 2} : Finset (Fin 1982)) := by
    by_contra hcon
    have hsub : s ⊆ ({0, 1, 2} : Finset (Fin 1982)) := by
      intro x hx
      by_contra hxnot
      exact hcon ⟨x, hx, hxnot⟩
    have hle := Finset.card_le_card hsub
    rw [hs, card_three] at hle
    exact absurd hle (by norm_num)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hvnot
  obtain ⟨h0, h1, h2⟩ := hvnot
  exact ⟨v, hv, fun w _ hwv => (extremal_universal_iff v).mpr ⟨h0, h1, h2⟩ w hwv⟩

/-- The extremal graph has exactly 1979 universal vertices. -/
lemma extremal_count :
    (Finset.univ.filter (IsUniversal extremalGraph)).card = 1979 := by
  have h1 : Finset.univ.filter (IsUniversal extremalGraph) =
      Finset.univ \ ({0, 1, 2} : Finset (Fin 1982)) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff,
      Finset.mem_insert, Finset.mem_singleton]
    rw [extremal_universal_iff v]
    tauto
  rw [h1, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin,
    card_three]

snip end

problem usa1982_p1 :
    IsLeast {n : ℕ | ∃ G : SimpleGraph (Fin 1982), FourPointProperty G ∧
      n = (Finset.univ.filter (IsUniversal G)).card} solution := by
  constructor
  · exact ⟨extremalGraph, extremal_fourPoint, extremal_count.symm⟩
  · intro n hn
    obtain ⟨G, hG, hn⟩ := hn
    rw [hn]
    exact card_universal_ge G hG

end Usa1982P1
