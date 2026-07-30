/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Trails
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Algebra.GCDMonoid.Finset
public import ProblemExtraction

@[expose] public section

problem_file {
  tags := [.Combinatorics]
}

/-!
# International Mathematical Olympiad 1991, Problem 4

Suppose G is a connected graph with k edges. Prove that it is possible to
label the edges 1, 2, ... , k in such a way that at each vertex which belongs
to two or more edges, the greatest common divisor of the integers labeling
those edges is equal to 1.
-/

namespace Imo1991P4

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

snip begin

/-- The vertices that a walk visits at an interior position: all `w.getVert (i + 1)`
with `i + 1 < w.length`. At each such vertex two consecutive edges of the walk meet. -/
def interiorVerts {u v : V} (w : G.Walk u v) : Finset V :=
  (Finset.range (w.length - 1)).image (fun i => w.getVert (i + 1))

omit [Fintype V] [DecidableRel G.Adj] in
lemma mem_interiorVerts {u v : V} {w : G.Walk u v} {x : V} :
    x ∈ interiorVerts w ↔ ∃ i, i < w.length - 1 ∧ w.getVert (i + 1) = x := by
  simp [interiorVerts]

omit [Fintype V] [DecidableRel G.Adj] in
/-- Every vertex of a walk is its start, an interior vertex, or its end. -/
lemma start_or_interior_or_end {u v : V} {w : G.Walk u v} {x : V} (hx : x ∈ w.support) :
    x = u ∨ x ∈ interiorVerts w ∨ x = v := by
  have hidx : w.support.idxOf x < w.support.length := List.idxOf_lt_length_of_mem hx
  have hlen : w.support.length = w.length + 1 := w.length_support
  have hx2 : w.getVert (w.support.idxOf x) = x := w.getVert_support_idxOf hx
  set i := w.support.idxOf x with hi
  have hile : i ≤ w.length := by omega
  rcases Nat.lt_or_eq_of_le hile with hilt | hie
  · rcases Nat.eq_zero_or_pos i with hi0 | hipos
    · left
      rw [← hx2, hi0]
      exact w.getVert_zero
    · right; left
      rw [mem_interiorVerts]
      exact ⟨i - 1, by omega, by rw [Nat.sub_add_cancel hipos]; exact hx2⟩
  · right; right
    rw [← hx2, hie]
    exact w.getVert_length

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- The `i`-th edge of a walk joins its `i`-th and `(i + 1)`-th vertices. -/
lemma edges_getElem {u v : V} (w : G.Walk u v) (i : ℕ) (hi : i < w.edges.length) :
    w.edges[i] = s(w.getVert i, w.getVert (i + 1)) := by
  have hi' : i < w.darts.length := by rwa [w.length_darts, ← w.length_edges]
  show (w.darts.map Dart.edge)[i]'(by rw [List.length_map]; exact hi') = _
  rw [List.getElem_map, w.darts_getElem_eq_getVert i hi', Dart.edge_mk]

/-- The number of edges of a trail is at most the number of edges of the graph. -/
lemma trail_length_le_card {u v : V} (w : G.Walk u v) (hw : w.IsTrail) :
    w.length ≤ G.edgeFinset.card := by
  rw [← w.length_edges, ← List.toFinset_card_of_nodup hw.edges_nodup]
  apply Finset.card_le_card
  intro e he
  rw [List.mem_toFinset] at he
  rw [SimpleGraph.mem_edgeFinset]
  exact w.edges_subset_edgeSet he

/-- A maximal-length trail starting from `s₀`, which exists whenever `s₀` has an
incident edge. It ends at a vertex all of whose incident edges are used by the trail. -/
lemma exists_maximal_trail {s₀ : V} (h : ∃ x, G.Adj s₀ x) :
    ∃ (t : V) (w : G.Walk s₀ t), w.IsTrail ∧ 1 ≤ w.length ∧
      ∀ x : V, G.Adj t x → s(t, x) ∈ w.edges := by
  classical
  set T := (Finset.range (G.edgeFinset.card + 1)).filter
    (fun m => ∃ t, ∃ w : G.Walk s₀ t, w.IsTrail ∧ w.length = m) with hTdef
  have h0T : 0 ∈ T := by
    simp only [hTdef, mem_filter, mem_range, Nat.zero_lt_succ, true_and]
    exact ⟨s₀, Walk.nil, by simp, rfl⟩
  obtain ⟨x, hx⟩ := h
  have hcard : 0 < G.edgeFinset.card := by
    rw [Finset.card_pos]
    exact ⟨s(s₀, x), by rw [SimpleGraph.mem_edgeFinset]; exact G.mem_edgeSet.mpr hx⟩
  have h1T : 1 ∈ T := by
    simp only [hTdef, mem_filter, mem_range]
    refine ⟨by omega, x, Walk.cons hx Walk.nil, ?_, by simp⟩
    rw [Walk.isTrail_cons]
    simp
  obtain ⟨m, hmT, hmaxle⟩ : ∃ m, m ∈ T ∧ ∀ a ∈ T, a ≤ m :=
    ⟨T.max' ⟨0, h0T⟩, T.max'_mem _, fun a ha => T.le_max' a ha⟩
  have hmT' := hmT
  simp only [hTdef, mem_filter, mem_range] at hmT'
  obtain ⟨hmle, t, w, htrail, hlen⟩ := hmT'
  refine ⟨t, w, htrail, ?_, ?_⟩
  · have h1m : 1 ≤ m := hmaxle 1 h1T
    omega
  · intro x hx
    by_contra hmem
    have htrail' : (w.concat hx).IsTrail := by
      rw [Walk.concat_eq_append, Walk.isTrail_append]
      refine ⟨htrail, ?_, ?_⟩
      · rw [Walk.isTrail_cons]
        simp
      · simp only [Walk.edges_cons, Walk.edges_nil, List.disjoint_singleton]
        exact hmem
    have hlen' : (w.concat hx).length = m + 1 := by
      simp [Walk.concat_eq_append, hlen]
    have hmemT : m + 1 ∈ T := by
      simp only [hTdef, mem_filter, mem_range]
      have hb := trail_length_le_card (w.concat hx) htrail'
      rw [hlen'] at hb
      exact ⟨by omega, x, w.concat hx, htrail', hlen'⟩
    have := hmaxle (m + 1) hmemT
    omega

omit [Fintype V] [DecidableRel G.Adj] in
/-- Key walk lemma: from a vertex `u` that still has an edge outside the trail `w`,
one can walk to a vertex of `S`, to the start of `w`, or to an interior vertex of `w`,
using only edges outside the trail. -/
lemma find_good {s₀ t : V} (w : G.Walk s₀ t)
    (hmax : ∀ x : V, G.Adj t x → s(t, x) ∈ w.edges)
    (S : Finset V) {u z : V} (W : G.Walk u z) :
    (z ∈ S ∨ z ∈ w.support) → (∃ x, (G.deleteEdges (↑w.edges.toFinset)).Adj u x) →
    ∃ s', (s' ∈ S ∨ s' = s₀ ∨ s' ∈ interiorVerts w) ∧
      (G.deleteEdges (↑w.edges.toFinset)).Reachable u s' := by
  induction W with
  | nil =>
    intro hz hu
    rename_i uu
    obtain (h | h) := hz
    · exact ⟨uu, Or.inl h, SimpleGraph.Reachable.refl uu⟩
    · obtain (h1 | hi | h1) := start_or_interior_or_end h
      · exact ⟨uu, Or.inr (Or.inl h1), SimpleGraph.Reachable.refl uu⟩
      · exact ⟨uu, Or.inr (Or.inr hi), SimpleGraph.Reachable.refl uu⟩
      · rw [h1] at hu
        obtain ⟨x, hx⟩ := hu
        rw [SimpleGraph.deleteEdges_adj] at hx
        exact absurd (hmax x hx.1) (by simpa using hx.2)
  | @cons uu vv ww huv W' ih =>
    intro hz hu
    by_cases hedge : s(uu, vv) ∈ w.edges
    · have hus : uu ∈ w.support := w.fst_mem_support_of_mem_edges hedge
      obtain (h1 | hi | h1) := start_or_interior_or_end hus
      · exact ⟨uu, Or.inr (Or.inl h1), SimpleGraph.Reachable.refl uu⟩
      · exact ⟨uu, Or.inr (Or.inr hi), SimpleGraph.Reachable.refl uu⟩
      · rw [h1] at hu
        obtain ⟨x, hx⟩ := hu
        rw [SimpleGraph.deleteEdges_adj] at hx
        exact absurd (hmax x hx.1) (by simpa using hx.2)
    · have huv' : (G.deleteEdges (↑w.edges.toFinset)).Adj uu vv := by
        rw [SimpleGraph.deleteEdges_adj]
        exact ⟨huv, by simpa using hedge⟩
      by_cases hvv : vv ∈ S ∨ vv = s₀ ∨ vv ∈ interiorVerts w
      · exact ⟨vv, hvv, huv'.reachable⟩
      · have hvv1 : vv ∉ S := fun h => hvv (Or.inl h)
        have hvv2 : vv ≠ s₀ := fun h => hvv (Or.inr (Or.inl h))
        have hvv3 : vv ∉ interiorVerts w := fun h => hvv (Or.inr (Or.inr h))
        have hvv' : ∃ x, (G.deleteEdges (↑w.edges.toFinset)).Adj vv x := by
          cases W' with
          | nil =>
            obtain (h | h1) := hz
            · exact absurd h hvv1
            · obtain (h2 | hi | h2) := start_or_interior_or_end h1
              · exact absurd h2 hvv2
              · exact absurd hi hvv3
              · rw [h2] at huv'
                rw [SimpleGraph.deleteEdges_adj] at huv'
                exact absurd (hmax uu huv'.1.symm) (by simpa [Sym2.eq_swap] using huv'.2)
          | cons hvw W'' =>
            rename_i vv2
            by_cases h2 : s(vv, vv2) ∈ w.edges
            · have hsu' : vv ∈ w.support := w.fst_mem_support_of_mem_edges h2
              obtain (h3 | hi | h3) := start_or_interior_or_end hsu'
              · exact absurd h3 hvv2
              · exact absurd hi hvv3
              · rw [h3] at huv'
                rw [SimpleGraph.deleteEdges_adj] at huv'
                exact absurd (hmax uu huv'.1.symm) (by simpa [Sym2.eq_swap] using huv'.2)
            · exact ⟨vv2, by rw [SimpleGraph.deleteEdges_adj]; exact ⟨hvw, by simpa using h2⟩⟩
        obtain ⟨s', hs', hr⟩ := ih hz hvv'
        exact ⟨s', hs', huv'.reachable.trans hr⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Membership in the edge set of a graph with deleted edges. -/
lemma mem_edgeSet_deleteEdges {s : Set (Sym2 V)} {e : Sym2 V} :
    e ∈ (G.deleteEdges s).edgeSet ↔ e ∈ G.edgeSet ∧ e ∉ s := by
  induction e using Sym2.ind with
  | _ a b => simp

/-- The edge labeling given by a trail `w` (whose edges get the labels
`n + 1, …, n + w.length`, in order) together with a labeling `Φ'` of the
remaining edges. -/
def trailLabel {s₀ t : V} (w : G.Walk s₀ t) (n : ℕ) (Φ' : Sym2 V → ℕ) (e : Sym2 V) : ℕ :=
  if e ∈ w.edges then n + 1 + w.edges.idxOf e else Φ' e

omit [Fintype V] [DecidableRel G.Adj] in
lemma trailLabel_of_mem {s₀ t : V} {w : G.Walk s₀ t} {n : ℕ} {Φ' : Sym2 V → ℕ} {e : Sym2 V}
    (h : e ∈ w.edges) : trailLabel w n Φ' e = n + 1 + w.edges.idxOf e := by
  rw [trailLabel, if_pos h]

omit [Fintype V] [DecidableRel G.Adj] in
lemma trailLabel_of_not_mem {s₀ t : V} {w : G.Walk s₀ t} {n : ℕ} {Φ' : Sym2 V → ℕ} {e : Sym2 V}
    (h : e ∉ w.edges) : trailLabel w n Φ' e = Φ' e := by
  rw [trailLabel, if_neg h]

omit [Fintype V] [DecidableEq V] in
/-- If two elements of a finset have consecutive labels, the gcd of all labels is 1. -/
lemma gcd_eq_one_of_consecutive {s : Finset (Sym2 V)} {Φ : Sym2 V → ℕ} {e₁ e₂ : Sym2 V}
    (he₁ : e₁ ∈ s) (he₂ : e₂ ∈ s) (h : Φ e₁ + 1 = Φ e₂) :
    s.gcd Φ = 1 := by
  have d1 : s.gcd Φ ∣ Φ e₁ := Finset.gcd_dvd he₁
  have d2 : s.gcd Φ ∣ Φ e₂ := Finset.gcd_dvd he₂
  have hsub : Φ e₂ - Φ e₁ = 1 := by omega
  have h3 := Nat.dvd_sub d2 d1
  rw [hsub] at h3
  exact Nat.dvd_one.mp h3

omit [Fintype V] [DecidableEq V] in
/-- If some element of a finset has label 1, the gcd of all labels is 1. -/
lemma gcd_eq_one_of_eq_one {s : Finset (Sym2 V)} {Φ : Sym2 V → ℕ} {e : Sym2 V}
    (he : e ∈ s) (h : Φ e = 1) : s.gcd Φ = 1 := by
  have d : s.gcd Φ ∣ Φ e := Finset.gcd_dvd he
  rw [h] at d
  exact Nat.dvd_one.mp d

omit [Fintype V] in
/-- The gcd over a finset only depends on the values of the function on that finset. -/
lemma gcd_congr_on {s : Finset (Sym2 V)} {Φ Ψ : Sym2 V → ℕ} (h : ∀ e ∈ s, Φ e = Ψ e) :
    s.gcd Φ = s.gcd Ψ := by
  induction s using Finset.induction with
  | empty => simp
  | @insert a s has ih =>
    rw [Finset.gcd_insert, Finset.gcd_insert, h a (Finset.mem_insert_self a s),
      ih (fun e he => h e (Finset.mem_insert_of_mem he))]

/-- At an interior vertex of a trail, two consecutive edges meet, so the gcd of
the labels at that vertex is 1. -/
lemma gcd_interior {s₀ t : V} {w : G.Walk s₀ t} (htrail : w.IsTrail) {n : ℕ}
    {Φ' : Sym2 V → ℕ} {v : V} (hv : v ∈ interiorVerts w) :
    (G.incidenceFinset v).gcd (trailLabel w n Φ') = 1 := by
  rw [mem_interiorVerts] at hv
  obtain ⟨i, hilt, hiv⟩ := hv
  have hi1 : i < w.edges.length := by rw [w.length_edges]; omega
  have hi2 : i + 1 < w.edges.length := by rw [w.length_edges]; omega
  have e1inc : w.edges[i] ∈ G.incidenceFinset v := by
    rw [G.mem_incidenceFinset]
    exact ⟨w.edges_subset_edgeSet (List.getElem_mem _),
      by rw [edges_getElem w i hi1, ← hiv]; exact Sym2.mem_mk_right _ _⟩
  have e2inc : w.edges[i + 1] ∈ G.incidenceFinset v := by
    rw [G.mem_incidenceFinset]
    exact ⟨w.edges_subset_edgeSet (List.getElem_mem _),
      by rw [edges_getElem w (i + 1) hi2, ← hiv]; exact Sym2.mem_mk_left _ _⟩
  apply gcd_eq_one_of_consecutive e1inc e2inc
  rw [trailLabel_of_mem (List.getElem_mem _), htrail.edges_nodup.idxOf_getElem i hi1,
    trailLabel_of_mem (List.getElem_mem _), htrail.edges_nodup.idxOf_getElem (i + 1) hi2]
  rfl

/-- If a vertex `v` is neither the start, an interior vertex, nor the end of the
trail `w`, then no edge of the trail is incident to `v`. -/
lemma no_trail_edge_at {s₀ t : V} {w : G.Walk s₀ t} {v : V}
    (hvs : v ≠ s₀) (hvi : v ∉ interiorVerts w) (hvt : v ≠ t)
    {e : Sym2 V} (he : e ∈ G.incidenceFinset v) : e ∉ w.edges := by
  intro hew
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hew
  have hv2 := (G.mem_incidenceFinset v _).mp he |>.2
  rw [edges_getElem w j hj, Sym2.mem_iff] at hv2
  rcases hv2 with h | h
  · rcases Nat.eq_zero_or_pos j with hj0 | hjpos
    · rw [hj0, w.getVert_zero] at h
      exact hvs h
    · exact hvi (mem_interiorVerts.mpr
        ⟨j - 1, by have hle := w.length_edges; omega,
         by rw [Nat.sub_add_cancel hjpos]; exact h.symm⟩)
  · by_cases hjm : j + 1 = w.length
    · rw [hjm, w.getVert_length] at h
      exact hvt h
    · exact hvi (mem_interiorVerts.mpr ⟨j, by have hle := w.length_edges; omega, h.symm⟩)

/-- If all edges of the trail are incident to the endpoint `t` (maximality) and `t`
is neither the start nor an interior vertex, then at most one edge is incident to `t`. -/
lemma degree_endpoint_le_one {s₀ t : V} {w : G.Walk s₀ t}
    (hmax : ∀ x : V, G.Adj t x → s(t, x) ∈ w.edges)
    (hts : t ≠ s₀) (hti : t ∉ interiorVerts w) :
    (G.incidenceFinset t).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro e₁ he₁ e₂ he₂
  have key : ∀ e : Sym2 V, e ∈ G.edgeSet → t ∈ e →
      ∃ j : ℕ, ∃ hj : j < w.edges.length, w.edges[j] = e ∧ j = w.edges.length - 1 := by
    intro e he hed
    obtain ⟨x, rfl⟩ := Sym2.mem_iff_exists.mp hed
    rw [SimpleGraph.mem_edgeSet] at he
    obtain ⟨j, hj, hje⟩ := List.mem_iff_getElem.mp (hmax x he)
    rw [edges_getElem w j hj, Sym2.eq_iff] at hje
    rcases hje with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rcases Nat.eq_zero_or_pos j with hj0 | hjpos
      · rw [hj0, w.getVert_zero] at h1
        exact absurd h1.symm hts
      · exact absurd (mem_interiorVerts.mpr
          ⟨j - 1, by have hle := w.length_edges; omega,
           by rw [Nat.sub_add_cancel hjpos]; exact h1⟩) hti
    · by_cases hjm : j + 1 = w.length
      · have hjl' : j = w.edges.length - 1 := by have hle := w.length_edges; omega
        exact ⟨j, hj, by rw [edges_getElem w j hj, h1, h2]; exact Sym2.eq_swap, hjl'⟩
      · exact absurd (mem_interiorVerts.mpr
          ⟨j, by have hle := w.length_edges; omega, h2⟩) hti
  obtain ⟨j₁, hj₁, he₁q, hj₁q⟩ :=
    key e₁ ((G.mem_incidenceFinset t e₁).mp he₁).1 ((G.mem_incidenceFinset t e₁).mp he₁).2
  obtain ⟨j₂, hj₂, he₂q, hj₂q⟩ :=
    key e₂ ((G.mem_incidenceFinset t e₂).mp he₂).1 ((G.mem_incidenceFinset t e₂).mp he₂).2
  subst hj₁q
  subst hj₂q
  exact he₁q.symm.trans he₂q

/-- If no trail edge is incident to `v`, deleting the trail edges does not change
the incidence finset of `v`. -/
lemma incidenceFinset_deleteEdges_of_none {s₀ t : V} {w : G.Walk s₀ t} {v : V}
    (hnone : ∀ e ∈ G.incidenceFinset v, e ∉ w.edges) :
    G.incidenceFinset v = (G.deleteEdges (↑w.edges.toFinset)).incidenceFinset v := by
  ext e
  rw [G.mem_incidenceFinset, (G.deleteEdges (↑w.edges.toFinset)).mem_incidenceFinset]
  constructor
  · rintro ⟨he, hv⟩
    exact ⟨mem_edgeSet_deleteEdges.mpr ⟨he,
      by simpa using hnone e ((G.mem_incidenceFinset v e).mpr ⟨he, hv⟩)⟩, hv⟩
  · rintro ⟨he, hv⟩
    exact ⟨(mem_edgeSet_deleteEdges.mp he).1, hv⟩

/-- Transfer of the gcd computation to the graph with the trail edges deleted. -/
lemma gcd_transfer {s₀ t : V} {w : G.Walk s₀ t} {n : ℕ} {Φ' : Sym2 V → ℕ} {v : V}
    (hnone : ∀ e ∈ G.incidenceFinset v, e ∉ w.edges) :
    (G.incidenceFinset v).gcd (trailLabel w n Φ') =
      ((G.deleteEdges (↑w.edges.toFinset)).incidenceFinset v).gcd Φ' := by
  have hfin := incidenceFinset_deleteEdges_of_none hnone
  rw [hfin]
  apply gcd_congr_on
  intro e he
  exact trailLabel_of_not_mem (hnone e (hfin.symm ▸ he))

/-- The edge finset of a graph with the trail edges deleted. -/
lemma edgeFinset_deleteEdges_trail {s₀ t : V} {w : G.Walk s₀ t} :
    (G.deleteEdges (↑w.edges.toFinset)).edgeFinset = G.edgeFinset \ w.edges.toFinset := by
  ext e
  simp only [Finset.mem_sdiff, List.mem_toFinset, SimpleGraph.mem_edgeFinset,
    Finset.mem_coe, mem_edgeSet_deleteEdges]

/-- Main induction: in any graph where every component that contains an edge meets
the set `S`, the edges can be labeled with `n + 1, …, n + k` in such a way that at
every vertex outside `S` of degree at least two the gcd of the labels is 1. -/
theorem exists_labeling : ∀ (k : ℕ) (H : SimpleGraph V) [DecidableRel H.Adj] (S : Finset V),
    H.edgeFinset.card = k →
    (∀ u v : V, H.Adj u v → ∃ s ∈ S, H.Reachable u s) →
    ∀ n : ℕ, ∃ Φ : Sym2 V → ℕ,
      (∀ e ∈ H.edgeSet, n + 1 ≤ Φ e ∧ Φ e ≤ n + k) ∧
      (∀ e₁ ∈ H.edgeSet, ∀ e₂ ∈ H.edgeSet, Φ e₁ = Φ e₂ → e₁ = e₂) ∧
      (∀ v : V, v ∉ S → 2 ≤ H.degree v → (H.incidenceFinset v).gcd Φ = 1) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro H _ S hk hS n
    by_cases hk0 : k = 0
    · -- No edges: everything is vacuous.
      subst hk0
      have hfin : H.edgeFinset = ∅ := Finset.card_eq_zero.mp hk
      have hempty : ∀ e : Sym2 V, e ∉ H.edgeSet := by
        intro e he
        exact Finset.notMem_empty e (hfin ▸ H.mem_edgeFinset.mpr he)
      refine ⟨fun _ => 0, ?_, ?_, ?_⟩
      · intro e he
        exact absurd he (hempty e)
      · intro e₁ he₁ _ _ _
        exact absurd he₁ (hempty e₁)
      · intro v _ hdeg
        have h0 : H.degree v = 0 := by
          rw [← H.card_incidenceFinset_eq_degree, Finset.card_eq_zero]
          ext e
          rw [H.mem_incidenceFinset]
          simp [SimpleGraph.incidenceSet, hempty]
        omega
    · -- Pick an edge, get a vertex of `S` in its component, and take a maximal trail.
      have hcardpos : 0 < H.edgeFinset.card := hk ▸ Nat.pos_of_ne_zero hk0
      obtain ⟨e₀, he₀⟩ := Finset.card_pos.mp hcardpos
      obtain ⟨a, b, hab⟩ : ∃ a b, H.Adj a b := by
        induction e₀ using Sym2.ind with
        | _ a b => exact ⟨a, b, H.mem_edgeSet.mp (H.mem_edgeFinset.mp he₀)⟩
      obtain ⟨s₀, hs₀S, hs₀a⟩ := hS a b hab
      have hs₀edge : ∃ x, H.Adj s₀ x := by
        obtain ⟨W⟩ := hs₀a.symm
        by_cases hW : W.Nil
        · have hWs := Walk.Nil.eq hW
          subst hWs
          exact ⟨b, hab⟩
        · exact ⟨W.snd, W.adj_snd hW⟩
      obtain ⟨t, w, htrail, hmlen, hmax⟩ := exists_maximal_trail hs₀edge
      have hmlek : w.length ≤ k := by
        have := trail_length_le_card w htrail
        omega
      have hcard' : (H.deleteEdges (↑w.edges.toFinset)).edgeFinset.card = k - w.length := by
        have hsub : w.edges.toFinset ⊆ H.edgeFinset := by
          intro e he
          rw [List.mem_toFinset] at he
          rw [SimpleGraph.mem_edgeFinset]
          exact w.edges_subset_edgeSet he
        rw [edgeFinset_deleteEdges_trail, Finset.card_sdiff, Finset.inter_eq_left.mpr hsub,
          List.toFinset_card_of_nodup htrail.edges_nodup, w.length_edges, hk]
      have hcardlt : (H.deleteEdges (↑w.edges.toFinset)).edgeFinset.card < k := by omega
      have hS' : ∀ u v : V, (H.deleteEdges (↑w.edges.toFinset)).Adj u v →
          ∃ s ∈ S ∪ interiorVerts w, (H.deleteEdges (↑w.edges.toFinset)).Reachable u s := by
        intro u v huv
        have huvH : H.Adj u v := (H.deleteEdges_adj.mp huv).1
        obtain ⟨s, hsS, hsr⟩ := hS u v huvH
        obtain ⟨W⟩ := hsr
        obtain ⟨s', hs', hr⟩ := find_good w hmax S W (Or.inl hsS) ⟨v, huv⟩
        rcases hs' with h | h1 | h
        · exact ⟨s', Finset.mem_union_left _ h, hr⟩
        · exact ⟨s₀, Finset.mem_union_left _ hs₀S, h1 ▸ hr⟩
        · exact ⟨s', Finset.mem_union_right _ h, hr⟩
      obtain ⟨Φ', hΦ'b, hΦ'inj, hΦ'gcd⟩ :=
        ih _ hcardlt _ _ rfl hS' (n + w.length)
      refine ⟨trailLabel w n Φ', ?_, ?_, ?_⟩
      · -- Bounds.
        intro e he
        by_cases h : e ∈ w.edges
        · rw [trailLabel_of_mem h]
          have hle := w.length_edges
          have hi : w.edges.idxOf e < w.edges.length := List.idxOf_lt_length_of_mem h
          constructor <;> omega
        · rw [trailLabel_of_not_mem h]
          have he' : e ∈ (H.deleteEdges (↑w.edges.toFinset)).edgeSet :=
            mem_edgeSet_deleteEdges.mpr ⟨he, by simpa using h⟩
          obtain ⟨h1, h2⟩ := hΦ'b e he'
          constructor <;> omega
      · -- Injectivity.
        intro e₁ he₁ e₂ he₂ heq
        by_cases h1 : e₁ ∈ w.edges <;> by_cases h2 : e₂ ∈ w.edges
        · rw [trailLabel_of_mem h1, trailLabel_of_mem h2] at heq
          have hidx : w.edges.idxOf e₁ = w.edges.idxOf e₂ := by omega
          exact (List.idxOf_inj h1).mp hidx
        · rw [trailLabel_of_mem h1, trailLabel_of_not_mem h2] at heq
          have hle := w.length_edges
          have hi : w.edges.idxOf e₁ < w.edges.length := List.idxOf_lt_length_of_mem h1
          have he₂' : e₂ ∈ (H.deleteEdges (↑w.edges.toFinset)).edgeSet :=
            mem_edgeSet_deleteEdges.mpr ⟨he₂, by simpa using h2⟩
          have hlo := (hΦ'b e₂ he₂').1
          omega
        · rw [trailLabel_of_not_mem h1, trailLabel_of_mem h2] at heq
          have hle := w.length_edges
          have hi : w.edges.idxOf e₂ < w.edges.length := List.idxOf_lt_length_of_mem h2
          have he₁' : e₁ ∈ (H.deleteEdges (↑w.edges.toFinset)).edgeSet :=
            mem_edgeSet_deleteEdges.mpr ⟨he₁, by simpa using h1⟩
          have hlo := (hΦ'b e₁ he₁').1
          omega
        · rw [trailLabel_of_not_mem h1, trailLabel_of_not_mem h2] at heq
          have he₁' : e₁ ∈ (H.deleteEdges (↑w.edges.toFinset)).edgeSet :=
            mem_edgeSet_deleteEdges.mpr ⟨he₁, by simpa using h1⟩
          have he₂' : e₂ ∈ (H.deleteEdges (↑w.edges.toFinset)).edgeSet :=
            mem_edgeSet_deleteEdges.mpr ⟨he₂, by simpa using h2⟩
          exact hΦ'inj e₁ he₁' e₂ he₂' heq
      · -- The gcd condition.
        intro v hvS hdeg
        by_cases hvi : v ∈ interiorVerts w
        · exact gcd_interior htrail hvi
        · by_cases hvt : v = t
          · subst hvt
            have hts : v ≠ s₀ := fun h => hvS (h ▸ hs₀S)
            have h1 := degree_endpoint_le_one hmax hts hvi
            rw [H.card_incidenceFinset_eq_degree] at h1
            omega
          · have hvs : v ≠ s₀ := fun h => hvS (h ▸ hs₀S)
            have hnone : ∀ e ∈ H.incidenceFinset v, e ∉ w.edges :=
              fun e he => no_trail_edge_at hvs hvi hvt he
            have hfin := incidenceFinset_deleteEdges_of_none hnone
            have hdeg' : 2 ≤ (H.deleteEdges (↑w.edges.toFinset)).degree v := by
              rw [← (H.deleteEdges (↑w.edges.toFinset)).card_incidenceFinset_eq_degree, ← hfin,
                H.card_incidenceFinset_eq_degree]
              exact hdeg
            have hvS' : v ∉ S ∪ interiorVerts w := by simp [hvS, hvi]
            have hg := hΦ'gcd v hvS' hdeg'
            rw [← hg]
            exact gcd_transfer hnone

snip end

problem imo1991_p4 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : G.Connected) :
    ∃ Φ : Sym2 V → ℕ,
      (∀ e ∈ G.edgeSet, 1 ≤ Φ e ∧ Φ e ≤ Fintype.card G.edgeSet) ∧
      (∀ e₁ ∈ G.edgeSet, ∀ e₂ ∈ G.edgeSet, Φ e₁ = Φ e₂ → e₁ = e₂) ∧
      (∀ v : V, 2 ≤ G.degree v → (G.incidenceFinset v).gcd Φ = 1) := by
  have hcard : G.edgeFinset.card = Fintype.card G.edgeSet := Set.toFinset_card _
  by_cases hk0 : G.edgeFinset.card = 0
  · -- No edges: everything is vacuous.
    have hfin : G.edgeFinset = ∅ := Finset.card_eq_zero.mp hk0
    have hempty : ∀ e : Sym2 V, e ∉ G.edgeSet := by
      intro e he
      exact Finset.notMem_empty e (hfin ▸ G.mem_edgeFinset.mpr he)
    refine ⟨fun _ => 0, ?_, ?_, ?_⟩
    · intro e he
      exact absurd he (hempty e)
    · intro e₁ he₁ _ _ _
      exact absurd he₁ (hempty e₁)
    · intro v hdeg
      have h0 : G.degree v = 0 := by
        rw [← G.card_incidenceFinset_eq_degree, Finset.card_eq_zero]
        ext e
        rw [G.mem_incidenceFinset]
        simp [SimpleGraph.incidenceSet, hempty]
      omega
  · -- Take a maximal trail from an endpoint of some edge, then apply the induction.
    have hcardpos : 0 < G.edgeFinset.card := Nat.pos_of_ne_zero hk0
    obtain ⟨e₀, he₀⟩ := Finset.card_pos.mp hcardpos
    obtain ⟨a, b, hab⟩ : ∃ a b, G.Adj a b := by
      induction e₀ using Sym2.ind with
      | _ a b => exact ⟨a, b, G.mem_edgeSet.mp (G.mem_edgeFinset.mp he₀)⟩
    obtain ⟨t, w, htrail, hmlen, hmax⟩ := exists_maximal_trail ⟨b, hab⟩
    have hS' : ∀ u v : V, (G.deleteEdges (↑w.edges.toFinset)).Adj u v →
        ∃ s ∈ insert a (interiorVerts w), (G.deleteEdges (↑w.edges.toFinset)).Reachable u s := by
      intro u v huv
      have hreach : G.Reachable u a := hG u a
      obtain ⟨W⟩ := hreach
      obtain ⟨s', hs', hr⟩ := find_good w hmax ∅ W (Or.inr w.start_mem_support) ⟨v, huv⟩
      rcases hs' with h | h1 | h
      · exact absurd h (Finset.notMem_empty _)
      · exact ⟨a, Finset.mem_insert_self a _, h1 ▸ hr⟩
      · exact ⟨s', Finset.mem_insert_of_mem h, hr⟩
    obtain ⟨Φ', hΦ'b, hΦ'inj, hΦ'gcd⟩ :=
      exists_labeling (G.deleteEdges (↑w.edges.toFinset)).edgeFinset.card _ _ rfl hS' w.length
    have hmlek : w.length ≤ G.edgeFinset.card := trail_length_le_card w htrail
    have hcard' : (G.deleteEdges (↑w.edges.toFinset)).edgeFinset.card =
        G.edgeFinset.card - w.length := by
      have hsub : w.edges.toFinset ⊆ G.edgeFinset := by
        intro e he
        rw [List.mem_toFinset] at he
        rw [SimpleGraph.mem_edgeFinset]
        exact w.edges_subset_edgeSet he
      rw [edgeFinset_deleteEdges_trail, Finset.card_sdiff, Finset.inter_eq_left.mpr hsub,
        List.toFinset_card_of_nodup htrail.edges_nodup, w.length_edges]
    refine ⟨trailLabel w 0 Φ', ?_, ?_, ?_⟩
    · -- Bounds.
      intro e he
      by_cases h : e ∈ w.edges
      · rw [trailLabel_of_mem h]
        have hle := w.length_edges
        have hi : w.edges.idxOf e < w.edges.length := List.idxOf_lt_length_of_mem h
        rw [← hcard]
        constructor <;> omega
      · rw [trailLabel_of_not_mem h]
        have he' : e ∈ (G.deleteEdges (↑w.edges.toFinset)).edgeSet :=
          mem_edgeSet_deleteEdges.mpr ⟨he, by simpa using h⟩
        obtain ⟨h1, h2⟩ := hΦ'b e he'
        rw [← hcard]
        constructor <;> omega
    · -- Injectivity.
      intro e₁ he₁ e₂ he₂ heq
      by_cases h1 : e₁ ∈ w.edges <;> by_cases h2 : e₂ ∈ w.edges
      · rw [trailLabel_of_mem h1, trailLabel_of_mem h2] at heq
        have hidx : w.edges.idxOf e₁ = w.edges.idxOf e₂ := by omega
        exact (List.idxOf_inj h1).mp hidx
      · rw [trailLabel_of_mem h1, trailLabel_of_not_mem h2] at heq
        have hle := w.length_edges
        have hi : w.edges.idxOf e₁ < w.edges.length := List.idxOf_lt_length_of_mem h1
        have he₂' : e₂ ∈ (G.deleteEdges (↑w.edges.toFinset)).edgeSet :=
          mem_edgeSet_deleteEdges.mpr ⟨he₂, by simpa using h2⟩
        have hlo := (hΦ'b e₂ he₂').1
        omega
      · rw [trailLabel_of_not_mem h1, trailLabel_of_mem h2] at heq
        have hle := w.length_edges
        have hi : w.edges.idxOf e₂ < w.edges.length := List.idxOf_lt_length_of_mem h2
        have he₁' : e₁ ∈ (G.deleteEdges (↑w.edges.toFinset)).edgeSet :=
          mem_edgeSet_deleteEdges.mpr ⟨he₁, by simpa using h1⟩
        have hlo := (hΦ'b e₁ he₁').1
        omega
      · rw [trailLabel_of_not_mem h1, trailLabel_of_not_mem h2] at heq
        have he₁' : e₁ ∈ (G.deleteEdges (↑w.edges.toFinset)).edgeSet :=
          mem_edgeSet_deleteEdges.mpr ⟨he₁, by simpa using h1⟩
        have he₂' : e₂ ∈ (G.deleteEdges (↑w.edges.toFinset)).edgeSet :=
          mem_edgeSet_deleteEdges.mpr ⟨he₂, by simpa using h2⟩
        exact hΦ'inj e₁ he₁' e₂ he₂' heq
    · -- The gcd condition.
      intro v hdeg
      by_cases hva : v = a
      · subst hva
        have h0len : 0 < w.edges.length := by rw [w.length_edges]; omega
        have hmem : w.edges[0]'h0len ∈ G.incidenceFinset v := by
          rw [G.mem_incidenceFinset]
          exact ⟨w.edges_subset_edgeSet (List.getElem_mem _),
            by rw [edges_getElem w 0 h0len, w.getVert_zero]; exact Sym2.mem_mk_left _ _⟩
        apply gcd_eq_one_of_eq_one hmem
        rw [trailLabel_of_mem (List.getElem_mem _), htrail.edges_nodup.idxOf_getElem 0 h0len]
      · by_cases hvi : v ∈ interiorVerts w
        · exact gcd_interior htrail hvi
        · by_cases hvt : v = t
          · subst hvt
            have h1 := degree_endpoint_le_one hmax hva hvi
            rw [G.card_incidenceFinset_eq_degree] at h1
            omega
          · have hnone : ∀ e ∈ G.incidenceFinset v, e ∉ w.edges :=
              fun e he => no_trail_edge_at hva hvi hvt he
            have hfin := incidenceFinset_deleteEdges_of_none hnone
            have hdeg' : 2 ≤ (G.deleteEdges (↑w.edges.toFinset)).degree v := by
              rw [← (G.deleteEdges (↑w.edges.toFinset)).card_incidenceFinset_eq_degree, ← hfin,
                G.card_incidenceFinset_eq_degree]
              exact hdeg
            have hvS' : v ∉ insert a (interiorVerts w) := by simp [hva, hvi]
            have hg := hΦ'gcd v hvS' hdeg'
            rw [← hg]
            exact gcd_transfer hnone

end Imo1991P4
