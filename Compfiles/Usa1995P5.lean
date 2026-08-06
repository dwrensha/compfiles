/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics] }

/-!
# USA Mathematical Olympiad 1995, Problem 5

A graph with n points and k edges has no triangles. Show that it has a
point P such that there are at most k(1 - 4k/n²) edges between points
not joined to P (by an edge).
-/

namespace Usa1995P5

open Finset SimpleGraph

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

snip begin

/-- In a triangle-free graph, no edge can have two distinct endpoints that are
both adjacent to `P`: together with `P` they would form a triangle. -/
lemma not_adj_and_adj_of_mem_edgeFinset (hG : G.CliqueFree 3) {P Q₁ Q₂ : Fin n}
    (hPQ₁ : G.Adj P Q₁) (hPQ₂ : G.Adj P Q₂) (hne : Q₁ ≠ Q₂)
    {e : Sym2 (Fin n)} (he : e ∈ G.edgeFinset) (h₁ : Q₁ ∈ e) (h₂ : Q₂ ∈ e) :
    False := by
  induction e using Sym2.ind with
  | h a b =>
    rw [mem_edgeFinset, mem_edgeSet] at he
    rw [Sym2.mem_iff] at h₁ h₂
    have hAdj : G.Adj Q₁ Q₂ := by
      rcases h₁ with rfl | rfl <;> rcases h₂ with rfl | rfl
      · exact absurd rfl hne
      · exact he
      · exact he.symm
      · exact absurd rfl hne
    exact hG _ (is3Clique_triple_iff.mpr ⟨hPQ₁, hPQ₂, hAdj⟩)

/-- Double counting: the sum of the degrees of the neighbors of `P` equals the
number of edges of `G` having an endpoint adjacent to `P`. Indeed, every edge
incident to a neighbor `Q` of `P` has `Q` as its *unique* endpoint adjacent to
`P`, since the graph is triangle-free. -/
lemma sum_degree_neighborFinset_eq_card (hG : G.CliqueFree 3) (P : Fin n) :
    ∑ Q ∈ G.neighborFinset P, G.degree Q
      = #(G.edgeFinset.filter fun e => ∃ v ∈ e, G.Adj P v) := by
  have hdeg : ∀ Q : Fin n, G.degree Q = #(G.edgeFinset.filter fun e => Q ∈ e) := by
    intro Q
    rw [← card_incidenceFinset_eq_degree, incidenceFinset_eq_filter]
  simp_rw [hdeg]
  have hdisj : (↑(G.neighborFinset P) : Set (Fin n)).PairwiseDisjoint
      (fun Q => G.edgeFinset.filter fun e => Q ∈ e) := by
    intro Q₁ hQ₁ Q₂ hQ₂ hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    rintro e he₁ he₂
    rw [Finset.mem_filter] at he₁ he₂
    exact not_adj_and_adj_of_mem_edgeFinset G hG
      ((mem_neighborFinset G P Q₁).mp (Finset.mem_coe.mp hQ₁))
      ((mem_neighborFinset G P Q₂).mp (Finset.mem_coe.mp hQ₂)) hne he₁.1 he₁.2 he₂.2
  rw [← Finset.card_biUnion hdisj]
  congr 1
  ext e
  simp only [Finset.mem_biUnion, Finset.mem_filter, mem_neighborFinset]
  constructor
  · rintro ⟨Q, hPQ, he, hQe⟩
    exact ⟨he, Q, hQe, hPQ⟩
  · rintro ⟨he, Q, hQe, hPQ⟩
    exact ⟨Q, hPQ, he, hQe⟩

/-- The edges of `G` split into those with no endpoint adjacent to `P` and
those with a (unique) endpoint adjacent to `P`, counted in
`sum_degree_neighborFinset_eq_card`. -/
lemma card_far_add_sum_degree (hG : G.CliqueFree 3) (P : Fin n) :
    #(G.edgeFinset.filter fun e => ∀ v ∈ e, ¬G.Adj P v)
      + ∑ Q ∈ G.neighborFinset P, G.degree Q = #G.edgeFinset := by
  have hfar : (G.edgeFinset.filter fun e => ∀ v ∈ e, ¬G.Adj P v)
      = G.edgeFinset.filter fun e => ¬∃ v ∈ e, G.Adj P v :=
    Finset.filter_congr fun e _ => by simp only [not_exists, not_and]
  have hcard := Finset.card_filter_add_card_filter_not (s := G.edgeFinset)
    (p := fun e => ∃ v ∈ e, G.Adj P v)
  rw [hfar, sum_degree_neighborFinset_eq_card G hG P, add_comm]
  exact hcard

/-- Summing `∑ Q ∈ N(P), deg Q` over all vertices `P` counts `deg Q` once for
each neighbor of `Q`, giving the sum of the squares of the degrees. -/
lemma sum_sum_degree_neighborFinset :
    ∑ P : Fin n, ∑ Q ∈ G.neighborFinset P, G.degree Q
      = ∑ Q : Fin n, (G.degree Q) ^ 2 := by
  have hswap : ∀ Q : Fin n,
      (∑ P : Fin n, if G.Adj P Q then G.degree Q else 0) = (G.degree Q) ^ 2 := by
    intro Q
    have h : (Finset.univ.filter fun P => G.Adj P Q) = G.neighborFinset Q := by
      ext P
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_neighborFinset]
      exact SimpleGraph.adj_comm G P Q
    rw [← Finset.sum_filter, h, Finset.sum_const, card_neighborFinset_eq_degree,
      nsmul_eq_mul, pow_two, Nat.cast_id]
  simp_rw [neighborFinset_eq_filter, Finset.sum_filter]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun Q _ => hswap Q

snip end

problem usa1995_p5 {n : ℕ} [NeZero n] (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hG : G.CliqueFree 3) :
    ∃ P : Fin n,
      (#(G.edgeFinset.filter fun e => ∀ v ∈ e, ¬G.Adj P v) : ℝ)
        ≤ (#G.edgeFinset : ℝ) * (1 - 4 * #G.edgeFinset / n ^ 2) := by
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (NeZero.pos n)
  set k : ℝ := (#G.edgeFinset : ℝ) with hk
  -- Double counting, summed over all vertices.
  have hB : (∑ P : Fin n, ∑ Q ∈ G.neighborFinset P, (G.degree Q : ℝ))
      = ∑ Q : Fin n, (G.degree Q : ℝ) ^ 2 := by
    exact_mod_cast sum_sum_degree_neighborFinset G
  -- Cauchy–Schwarz.
  have hCS : (∑ Q : Fin n, (G.degree Q : ℝ)) ^ 2
      ≤ n * ∑ Q : Fin n, (G.degree Q : ℝ) ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n))
      (fun Q => (G.degree Q : ℝ)) 1
    simp only [Pi.one_apply, mul_one, one_pow, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, Fintype.card_fin] at h
    rwa [mul_comm] at h
  -- The handshaking lemma.
  have hHand : (∑ Q : Fin n, (G.degree Q : ℝ)) = 2 * k := by
    rw [hk]
    exact_mod_cast sum_degrees_eq_twice_card_edges G
  -- Averaging: some vertex `P` has `∑ Q ∈ N(P), deg Q ≥ 4k²/n²`.
  have hAvg : (∑ _P : Fin n, (4 * k ^ 2 / (n : ℝ) ^ 2))
      ≤ ∑ P : Fin n, ∑ Q ∈ G.neighborFinset P, (G.degree Q : ℝ) := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_fin]
    rw [show (n : ℝ) * (4 * k ^ 2 / (n : ℝ) ^ 2) = 4 * k ^ 2 / n by field_simp]
    rw [div_le_iff₀ hnpos]
    have h4 : 4 * k ^ 2 ≤ (∑ P : Fin n, ∑ Q ∈ G.neighborFinset P,
        (G.degree Q : ℝ)) * n := by
      have h2 := hCS
      rw [hHand, ← hB] at h2
      nlinarith [h2]
    exact h4
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := by
    have : Nonempty (Fin n) := ⟨⟨0, NeZero.pos n⟩⟩
    exact Finset.univ_nonempty
  obtain ⟨P, -, hP⟩ := Finset.exists_le_of_sum_le hne hAvg
  -- For this `P`, the number of "far" edges is `k - ∑ Q ∈ N(P), deg Q`.
  refine ⟨P, ?_⟩
  have hsum := card_far_add_sum_degree G hG P
  have hsumℝ : (#(G.edgeFinset.filter fun e => ∀ v ∈ e, ¬G.Adj P v) : ℝ)
      + ∑ Q ∈ G.neighborFinset P, (G.degree Q : ℝ) = k := by
    rw [hk]
    exact_mod_cast hsum
  have htarget : k * (1 - 4 * k / (n : ℝ) ^ 2) = k - 4 * k ^ 2 / (n : ℝ) ^ 2 := by
    field_simp
  rw [htarget]
  linarith

end Usa1995P5
