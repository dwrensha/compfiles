/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: sjfhsjfh
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# China Pre-CMO (National High School Math League, Second Round) 2000, Problem 3

有 n 个人，已知他们中的任意两人至多通电话一次，
他们中的任意 n−2 个人之间通电话的总次数相等，都是 3ᵏ 次，
其中 k 是自然数（注：当时自然数定义不含 0，即 k ≥ 1）。
求 n 的所有可能值。

There are n people, and any two of them have made at most one phone call with each other.
For any group of n−2 people, the total number of phone calls among them is the same,
all equal to 3ᵏ, where k is a positive integer (note: at the time, 0 was not considered
a natural number).
Determine all possible values of n.
-/

namespace ChinaPre2000P3

open Finset

/-- Number of edges in the subgraph induced by `S` — each edge `{u,v} ⊆ S` is counted once. -/
def inducedEdges {n : ℕ}
  (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) [Fintype G.edgeSet] : ℕ :=
  ((G.edgeFinset).filter (fun e => e.toFinset ⊆ S)).card

determine answer : Set ℕ := {5}

snip begin

lemma powmod (b : ℕ) : (3 ^ b % 3 = 1 ∧ b = 0) ∨ 3 ^ b % 3 = 0 := by
  by_cases! hb : b = 0
  · subst hb; simp only [pow_zero, Nat.one_mod, and_self, one_ne_zero, or_false]
  obtain ⟨c, hc⟩ := Nat.exists_eq_succ_of_ne_zero hb
  refine Or.inr ?_
  subst hc; rewrite [Nat.succ_eq_add_one, pow_add, pow_one]
  exact Nat.mul_mod_left (3 ^ c) 3

lemma nat (n : ℕ) (hn : n > 3)
  (h : ∃ m k : ℕ, (n - 2) * (n - 3) * m = n * (n - 1) * 3 ^ k)
  : n = 4 ∨ n = 5 := by
  let n' := n - 3
  simp_all [show n = n' + 3 by omega]
  obtain ⟨m, k, h⟩ := h
  have hl : n' + 1 ∣ 2 * 3 ^ k := by
    rewrite [
      Nat.dvd_add_iff_right <| Nat.dvd_mul_right (n' + 1) (3 ^ k),
      ← Nat.add_mul, show n' + 1 + 2 = n' + 3 by omega,
      Nat.dvd_add_iff_right <| Nat.dvd_mul_right (n' + 1) ((n' + 3) * 3 ^ k),
      ← Nat.add_one_mul, ← mul_assoc, show n' + 1 + 1 = n' + 2 by omega,
      mul_comm (n' + 2) (n' + 3),
    ]; exact dvd_of_mul_right_dvd <| Dvd.intro _ h
  have hr : n' ∣ 2 * 3 ^ (k + 1) := by
    rewrite [
      pow_add, pow_one, mul_comm _ 3, ← mul_assoc, mul_comm 2 3, mul_assoc,
      Nat.dvd_add_iff_right <| Nat.dvd_mul_right n' (2 * 3 ^ k),
      ← Nat.add_mul, mul_comm (n' + 3) _, mul_assoc,
      Nat.dvd_add_iff_right <| Nat.dvd_mul_right n' (3 ^ k * (n' + 3)),
      ← Nat.add_mul, ← mul_assoc, mul_comm _ (n' + 3), ← mul_assoc,
    ]; exact dvd_of_mul_left_dvd <| Dvd.intro _ h
  obtain ⟨q, hq⟩ := Nat.even_or_odd' n'
  rcases hq.symm with (hq | hq)
  · refine Or.inl ?_; rewrite [hq]; simp
    rewrite [hq, show 2 * q + 1 + 1 = 2 * (q + 1) by omega] at hl
    obtain ⟨p, hp⟩ := Nat.dvd_of_mul_dvd_mul_left (by omega) hl
    rewrite [
      hq, pow_add, pow_one, hp, ← mul_assoc, ← mul_assoc,
      show 2 * (q + 1) = (2 * q + 1 + 1) by omega, mul_assoc, add_mul,
      ← Nat.dvd_add_iff_right <| Nat.dvd_mul_right (2 * q + 1) (p * 3),
      one_mul] at hr
    obtain ⟨u, hu⟩ := hr
    have : (q + 1) * (2 * q + 1) ∣ 3 ^ (k + 1) := by
      rewrite [Nat.pow_add_one, hp, mul_assoc, hu, ← mul_assoc]
      exact Nat.dvd_mul_right ((q + 1) * (2 * q + 1)) u
    obtain ⟨_, ⟨_, hmulp⟩⟩ := Nat.dvd_prime_pow Nat.prime_three |>.mp this
    obtain ⟨k1, ⟨_, hk1⟩⟩ := Nat.dvd_prime_pow Nat.prime_three |>.mp
      <| Dvd.intro _ hmulp
    obtain ⟨k2, ⟨_, hk2⟩⟩ := Nat.dvd_prime_pow Nat.prime_three |>.mp
      <| Dvd.intro_left _ hmulp
    have : 2 * 3 ^ k1 = 3 ^ k2 + 1 := by omega
    have := powmod k1
    have : (2 * 3 ^ k1 % 3 = 2 ∧ k1 = 0) ∨ 2 * 3 ^ k1 % 3 = 0 := by omega
    have := powmod k2
    have : ((3 ^ k2 + 1) % 3 = 1 ∧ k2 = 0) ∨ (3 ^ k2 + 1) % 3 = 2 := by omega
    have : k1 = 0 := by omega
    simpa only [this, pow_zero, Nat.add_eq_right] using hk1
  refine Or.inr ?_; rewrite [hq] at ⊢ hr hl; simp
  obtain ⟨p, hp⟩ := Nat.dvd_of_mul_dvd_mul_left (by omega) hr
  obtain ⟨u, hu⟩ := hl
  have : ¬ (Odd <| (2 * q + 1) * u) := by
    rewrite [← hu, Nat.not_odd_iff]
    exact Nat.mul_mod_right 2 (3 ^ k)
  have := Nat.odd_mul.not.mp this
  simp at this; obtain ⟨v, hv⟩ := this
  rewrite [hv, ← mul_two, mul_comm 2 _, ← mul_assoc] at hu
  have h : 3 ^ k = (2 * q + 1) * v := by omega
  rewrite [pow_add, h, pow_one] at hp
  have : q ∣ q * (2 * v * 3) + v * 3 := by
    rewrite [← mul_assoc, ← mul_assoc, mul_assoc (q * 2), mul_comm q 2,
    ← Nat.add_one_mul, ← mul_assoc]; exact Dvd.intro p (id (Eq.symm hp))
  have : q ∣ v * 3 := (Nat.dvd_add_iff_right <| Nat.dvd_mul_right q (2 * v * 3)).mpr this
  obtain ⟨w, hw⟩ := this
  have : 3 ^ (k + 1) = (2 * q + 1) * q * w := by
    rw [mul_assoc, ← hw, pow_add, pow_one, h, mul_assoc]
  have := Dvd.intro _ this.symm
  obtain ⟨_, ⟨_, hmulp⟩⟩ := Nat.dvd_prime_pow Nat.prime_three |>.mp this
  obtain ⟨k1, ⟨_, hk1⟩⟩ := Nat.dvd_prime_pow Nat.prime_three |>.mp
    <| Dvd.intro _ hmulp
  obtain ⟨k2, ⟨_, hk2⟩⟩ := Nat.dvd_prime_pow Nat.prime_three |>.mp
    <| Dvd.intro_left _ hmulp
  have : 2 * 3 ^ k2 + 1 = 3 ^ k1 := by omega
  have := powmod k1
  have := powmod k2
  have : ((2 * 3 ^ k2 + 1) % 3 = 0 ∧ k2 = 0)
    ∨ (2 * 3 ^ k2 + 1) % 3 = 1 := by omega
  by_cases! hk10 : k1 = 0
  · subst hk10; simp at hk1; subst hk1
    absurd Nat.pow_eq_zero.mp hk2.symm |>.left
    omega
  have : k2 = 0 := by omega
  subst this; simpa only using hk2

variable {n : ℕ} {G : SimpleGraph (Fin n)} [Fintype G.edgeSet]

lemma edgeCountLeUniv (S : Finset (Fin n))
  : inducedEdges G S ≤ inducedEdges G .univ := by
  simp only [inducedEdges, subset_univ, filter_true]
  exact card_filter_le G.edgeFinset fun e ↦ e.toFinset ⊆ S

lemma edgeCountUnivLeCG
  : inducedEdges G .univ ≤ n * (n - 1) / 2 := by
  simp only [inducedEdges, subset_univ, filter_true]
  let g : SimpleGraph (Fin n) := .completeGraph (Fin n)
  suffices h : g.edgeFinset.card = n.choose 2 by
    rewrite [← Nat.choose_two_right, ← h]
    refine card_le_card <| SimpleGraph.edgeFinset_mono ?_
    intro a b hG; simp [g]; exact SimpleGraph.Adj.ne hG
  rewrite [SimpleGraph.edgeFinset_card]
  simp [g, SimpleGraph.edgeSet, SimpleGraph.edgeSetEmbedding,
    Sym2.fromRel, Sym2.lift]
  rewrite [show n.choose 2 = (Fintype.card (Fin n)).choose 2 by
    rewrite [Fintype.card_fin n]; rfl, ← Sym2.card_subtype_not_diag]
  refine Fintype.card_congr' ?_
  congr 1; ext p;
  induction p using Sym2.ind with
  | h a b => simp

lemma hngtthree (h_cond : ∃ k : ℕ, 1 ≤ k ∧
    ∀ (S : Finset (Fin n)), S.card = n - 2 → inducedEdges G S = 3 ^ k)
  : n > 3 := by
  obtain ⟨_, ⟨_hk, hS⟩⟩ := h_cond
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_one.mpr _hk; subst hk
  by_cases! h2 : n ≤ 2
  · let S : Finset (Fin n) := .empty
    have hSempty : S = ∅ := by rfl
    have : n - 2 = 0 := by omega
    have : S.card = n - 2 := Eq.symm <| Eq.trans this <| Eq.symm <| card_eq_zero.mpr rfl
    simpa [inducedEdges, hSempty, pow_add] using hS S this
  by_cases! h3 : n = 3
  · subst h3
    simp only [Nat.reduceSub] at hS
    let S : Finset (Fin 3) := {0}
    have hScard : S.card = 1 := by exact card_singleton 0
    suffices hS' : inducedEdges G S = 0 by
      simp [hS S hScard] at hS'
    simp [inducedEdges, S]; intro p hp
    by_contra! h; absurd hp
    induction p using Sym2.ind with | h a b
    refine SimpleGraph.not_mem_edgeSet_of_isDiag G ?_
    by_contra h'; absurd Sym2.card_toFinset_of_not_isDiag _ h'
    simp [h]
  exact Nat.lt_of_le_of_ne h2 h3.symm

lemma hnnefour (h_cond : ∃ k : ℕ, 1 ≤ k ∧
    ∀ (S : Finset (Fin n)), S.card = n - 2 → inducedEdges G S = 3 ^ k)
  : n ≠ 4 := by
  by_contra! h; subst h; simp_all only [Nat.reduceSub]
  obtain ⟨k, ⟨hk, hS⟩⟩ := h_cond; absurd hk; rewrite [not_le, Nat.lt_one_iff]
  by_cases! hG : G = ⊥
  · let S : Finset (Fin 4) := {0, 1}
    suffices h : inducedEdges G S = 0 by
      simp [hS S (Nat.eq_of_beq_eq_true rfl).symm] at h
    subst hG; simp [inducedEdges]
  obtain ⟨a, b, hab⟩ := SimpleGraph.ne_bot_iff_exists_adj.mp hG
  let S : Finset (Fin 4) := {a, b}
  have hcardS : S.card = 2 := card_pair <| SimpleGraph.Adj.ne hab
  suffices h : inducedEdges G S = 1 by
    simpa [hS S hcardS] using h
  simp [inducedEdges, S, SimpleGraph.edgeFinset, Sym2.toFinset]
  refine card_eq_one.mpr ?_; use Sym2.mk a b
  refine eq_singleton_iff_unique_mem.mpr ⟨?_, ?_⟩
  · simp [hab, Sym2.toMultiset, Sym2.lift, Multiset.toFinset]
    refine subset_iff.mpr ?_; simp
  intro x; simp [Sym2.toMultiset, Sym2.lift, Multiset.toFinset]
  induction x using Sym2.ind with | h a' b'
  intro hab' hq; simp at hab'
  have ha' := @subset_iff.mp hq a' <| by simp
  have hb' := @subset_iff.mp hq b' <| by simp
  simp at ha'
  simp at hb'
  refine Sym2.eq_iff.mpr ?_
  rcases ha' with (h | h)
  <;> simp only [h, true_and, or_comm (a := _ ∧ _)]
  <;> refine Or.inl ?_ <;> subst h
  <;> simpa only [SimpleGraph.Adj.ne hab' |>.symm, false_or, or_false] using hb'

lemma choosetwo (n : ℕ) : n * (n - 1) = 2 * n.choose 2 := by
  have := Nat.choose_mul (n := n) (show 1 ≤ 2 by omega)
  simp at this; rewrite [← this, mul_comm]; rfl

lemma edgeFinset (e : Sym2 (Fin n))
  : ({v | v ∈ e} : Finset (Fin n)) = e.toFinset := by
  ext v; simp only [mem_filter, mem_univ, true_and, Sym2.mem_toFinset]

lemma edgeDisjoint (e : Sym2 (Fin n))
  : Disjoint e.toFinset ({x | x ∉ e} : Finset (Fin n)) := by
  rewrite [← compl_filter, edgeFinset e]; exact disjoint_compl_right

lemma count (m : ℕ) (hn : n > 3)
  (h : ∀ (S : Finset (Fin n)), S.card = n - 2 → inducedEdges G S = m)
  : (n - 2) * (n - 3) * inducedEdges G .univ = n * (n - 1) * m := by
  suffices h : (n - 2).choose 2 * inducedEdges G .univ = n.choose 2 * m by
    have : n - 3 = n - 2 - 1 := by omega
    rewrite [choosetwo n, this, choosetwo (n - 2), mul_assoc, mul_assoc]
    exact Nat.mul_right_inj (show 2 ≠ 0 by omega) |>.mpr h
  simp only [inducedEdges, subset_univ, filter_true]
  rewrite [
    show n.choose 2 = (powersetCard (n - 2) (.univ : Finset (Fin n))).card by
      rw [card_powersetCard, card_fin n, Nat.choose_symm (show n ≥ 2 by omega)],
    ← Nat.nsmul_eq_mul _ m, mul_comm, ← Nat.nsmul_eq_mul,
    ← sum_eq_card_nsmul (f := fun s ↦ inducedEdges G s) <| by
      intro s hs; refine h s (by simpa using hs),
    ← sum_eq_card_nsmul
      (f := fun e ↦ (powersetCard (n - 4) ({v | v ∉ e} : Finset (Fin n))).card) <| by
      intro e he; simp only [card_powersetCard]
      rewrite [← Nat.choose_symm (show n - 2 ≥ 2 by omega),
        show n - 2 - 2 = n - 4 by omega]; congr 1
      rewrite [show n - 2 = (.univ : Finset (Fin n)).card - e.toFinset.card by
        rewrite [card_fin n]; congr 1; simp [Sym2.card_toFinset];
        exact SimpleGraph.not_isDiag_of_mem_edgeFinset he]
      rewrite [← compl_filter, edgeFinset e]; exact Finset.card_compl _,
  ]
  unfold inducedEdges; simp only [← card_sigma]
  refine Finset.card_bij (fun ⟨e, rest⟩ he ↦ ⟨e.toFinset ∪ rest, e⟩) ?i ?inj ?surj
  case i =>
    intro ⟨e, rest⟩; simp; intro he hrest hrest'; refine ⟨?_, he⟩
    rewrite [
      show n - 2 = 2 + (n - 4) by omega, ← hrest',
      show 2 = e.toFinset.card by
        simpa [Sym2.card_toFinset] using G.not_isDiag_of_mem_edgeSet he,
    ]
    exact card_union_of_disjoint <| disjoint_of_subset_right hrest <| edgeDisjoint e
  case inj =>
    simp; intro ⟨e1, r1⟩ he1 hr1 hr1' ⟨e2, r2⟩ he2 hr2 hr2'; simp
    intro hunioneq heeq; subst heeq; simp_all only [true_and]
    conv at hunioneq =>
      rewrite [
        ← disjUnion_eq_union _ _ <| disjoint_of_subset_right hr1 <| edgeDisjoint e1,
        ← disjUnion_eq_union _ _ <| disjoint_of_subset_right hr2 <| edgeDisjoint e1,
        disjUnion_inj_right,
      ]
    exact hunioneq
  case surj =>
    intro ⟨vs, e⟩; simp; intro hv he hev; use vs \ e.toFinset; simp [hev, he]
    refine ⟨?_, ?_⟩
    · rewrite [← edgeFinset e, Finset.sdiff_eq_inter_compl, compl_filter]
      exact inter_subset_right
    rewrite [
      show n - 4 = n - 2 - 2 by omega, ← hv,
      show 2 = e.toFinset.card by
        simpa [Sym2.card_toFinset] using G.not_isDiag_of_mem_edgeSet he,
    ]
    exact card_sdiff_of_subset hev

snip end

problem chinaPre2000_p3 (n : ℕ) (G : SimpleGraph (Fin n))
  [DecidableRel G.Adj] [Fintype G.edgeSet]
  (h_cond : ∃ k : ℕ, 1 ≤ k ∧
    ∀ (S : Finset (Fin n)), S.card = n - 2 → inducedEdges G S = 3 ^ k)
  : n ∈ answer := by
  rewrite [Set.mem_singleton_iff]
  have hn : n > 3 := hngtthree h_cond
  have hn' := hnnefour h_cond
  obtain ⟨k, ⟨_, hS⟩⟩ := h_cond
  refine nat n hn (by use inducedEdges G .univ, k; exact count (3 ^ k) hn hS)
    |>.resolve_left hn'

end ChinaPre2000P3
