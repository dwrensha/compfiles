/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Data.Finset.Card
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Ring.Basic
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics] }

/-!
# USA Mathematical Olympiad 2007, Problem 3

Let S be a set containing n² + n − 1 elements. Suppose that the n-element
subsets of S are partitioned into two classes. Prove that there are at least
n pairwise disjoint sets in the same class.
-/

namespace Usa2007P3

snip begin

variable {α : Type*} [DecidableEq α]

/-- Any finite set `S` with `k * n ≤ S.card` contains `k` pairwise disjoint
`n`-element subsets (here `1 ≤ n`). -/
lemma exists_disjoint_family {n : ℕ} (hn : 1 ≤ n) :
    ∀ k : ℕ, ∀ S : Finset α, k * n ≤ S.card →
      ∃ F : Finset (Finset α), F.card = k ∧ (∀ A ∈ F, A ⊆ S ∧ A.card = n) ∧
        (F : Set (Finset α)).PairwiseDisjoint id := by
  intro k
  induction k with
  | zero =>
    intro S _
    exact ⟨∅, Finset.card_empty, fun A hA => (Finset.notMem_empty A hA).elim, by simp⟩
  | succ k ih =>
    intro S hS
    have hnS : n ≤ S.card := by
      have e : (k + 1) * n = k * n + n := by ring
      lia
    obtain ⟨A, hAS, hAcard⟩ := Finset.exists_subset_card_eq hnS
    have hS' : k * n ≤ (S \ A).card := by
      rw [Finset.card_sdiff_of_subset hAS, hAcard]
      have e : (k + 1) * n = k * n + n := by ring
      lia
    obtain ⟨F, hFcard, hFsub, hFdisj⟩ := ih (S \ A) hS'
    have hAnF : A ∉ F := by
      intro hA
      have hsub : A ⊆ A ∩ (S \ A) := Finset.subset_inter (Finset.Subset.refl A) (hFsub A hA).1
      have hempty : A ∩ (S \ A) = ∅ :=
        Finset.disjoint_iff_inter_eq_empty.mp Finset.disjoint_sdiff
      rw [hempty] at hsub
      have hAe : A = ∅ := Finset.subset_empty.mp hsub
      rw [hAe, Finset.card_empty] at hAcard
      lia
    refine ⟨insert A F, by rw [Finset.card_insert_of_notMem hAnF, hFcard], ?_, ?_⟩
    · intro D hD
      rw [Finset.mem_insert] at hD
      rcases hD with rfl | hD
      · exact ⟨hAS, hAcard⟩
      · exact ⟨(hFsub D hD).1.trans Finset.sdiff_subset, (hFsub D hD).2⟩
    · rw [Finset.coe_insert]
      refine Set.PairwiseDisjoint.insert hFdisj fun j hj _ => ?_
      show Disjoint A j
      exact Disjoint.mono (Finset.Subset.refl A) (hFsub j hj).1 Finset.disjoint_sdiff

/-- If every `(n+1)`-element subset `U` of `S` is monochromatic (i.e. all of its
`n`-element subsets have the same color), then all `n`-element subsets of `S` have
the same color: any two `n`-element sets can be joined by a chain in which
consecutive sets differ in exactly one element, so induction on the size of the
symmetric difference applies. -/
lemma color_eq (col : Finset α → Bool) {n : ℕ} {S : Finset α}
    (H : ∀ U : Finset α, U ⊆ S → U.card = n + 1 →
      ∀ A B : Finset α, A ⊆ U → B ⊆ U → A.card = n → B.card = n → col A = col B) :
    ∀ m : ℕ, ∀ A B : Finset α, A ⊆ S → B ⊆ S → A.card = n → B.card = n →
      (A \ B).card ≤ m → col A = col B := by
  intro m
  induction m with
  | zero =>
    intro A B _ _ hAcard hBcard hm
    have hAsubB : A ⊆ B := by
      rw [← Finset.sdiff_eq_empty_iff_subset, ← Finset.card_eq_zero]
      exact Nat.eq_zero_of_le_zero hm
    have hAeqB : A = B := Finset.eq_of_subset_of_card_le hAsubB (by lia)
    rw [hAeqB]
  | succ m ih =>
    intro A B hAS hBS hAcard hBcard hm
    by_cases hle : (A \ B).card ≤ m
    · exact ih A B hAS hBS hAcard hBcard hle
    · have hcard : (A \ B).card = m + 1 := by lia
      obtain ⟨a, ha⟩ : (A \ B).Nonempty := by
        rw [← Finset.card_pos, hcard]
        exact Nat.succ_pos m
      rw [Finset.mem_sdiff] at ha
      have hBAcard : (B \ A).card = (A \ B).card := by
        rw [Finset.card_sdiff (t := B) (s := A), Finset.card_sdiff (t := A) (s := B),
          Finset.inter_comm A B, hAcard, hBcard]
      obtain ⟨b, hb⟩ : (B \ A).Nonempty := by
        rw [← Finset.card_pos, hBAcard, hcard]
        exact Nat.succ_pos m
      rw [Finset.mem_sdiff] at hb
      have hb' : b ∉ A.erase a := by
        rw [Finset.mem_erase]
        exact fun h => hb.2 h.2
      have hn1 : 1 ≤ n := by
        have h0 : 0 < A.card := Finset.card_pos.mpr ⟨a, ha.1⟩
        lia
      have hA'card : (insert b (A.erase a)).card = n := by
        rw [Finset.card_insert_of_notMem hb', Finset.card_erase_of_mem ha.1]
        lia
      have hA'S : insert b (A.erase a) ⊆ S :=
        Finset.insert_subset (hBS hb.1) ((Finset.erase_subset a A).trans hAS)
      have hcol : col A = col (insert b (A.erase a)) := by
        apply H (insert b A) (Finset.insert_subset (hBS hb.1) hAS) _ A _
          (Finset.subset_insert b A) _ hAcard hA'card
        · rw [Finset.card_insert_of_notMem hb.2, hAcard]
        · exact Finset.insert_subset_insert b (Finset.erase_subset a A)
      have hA'B : ((insert b (A.erase a)) \ B).card ≤ m := by
        have e1 : (insert b (A.erase a)) \ B = (A \ B).erase a := by
          rw [Finset.insert_sdiff_of_mem _ hb.1, Finset.erase_sdiff_comm]
        have e2 : ((A \ B).erase a).card = m := by
          rw [Finset.card_erase_of_mem (Finset.mem_sdiff.mpr ha), hcard, Nat.add_sub_cancel]
        rw [e1, e2]
      have hcol2 : col (insert b (A.erase a)) = col B := ih _ B hA'S hBS hA'card hBcard hA'B
      rw [hcol, hcol2]

/-- The strengthened statement, proved by induction on `k`: if `S` has
`k * (n + 1) - 1` elements and the `n`-element subsets of `S` are two-colored
(by `col`), then one can find `k` pairwise disjoint `n`-element subsets of `S`
having the same color. -/
lemma main (col : Finset α → Bool) {n : ℕ} (hn : 1 ≤ n) :
    ∀ k : ℕ, ∀ S : Finset α, S.card = k * (n + 1) - 1 →
      ∃ F : Finset (Finset α), k ≤ F.card ∧ (∀ A ∈ F, A ⊆ S ∧ A.card = n) ∧
        (F : Set (Finset α)).PairwiseDisjoint id ∧ ∃ b : Bool, ∀ A ∈ F, col A = b := by
  intro k
  induction k with
  | zero =>
    intro S _
    exact ⟨∅, Nat.zero_le _, fun A hA => (Finset.notMem_empty A hA).elim, by simp,
      true, fun A hA => (Finset.notMem_empty A hA).elim⟩
  | succ k ih =>
    intro S hS
    by_contra h
    -- Every `(n+1)`-element subset `U` of `S` is monochromatic: the induction
    -- hypothesis gives `k` disjoint monochromatic sets in `S \ U`, and any
    -- `n`-subset of `U` sharing their color could be adjoined to them.
    have claim : ∀ U : Finset α, U ⊆ S → U.card = n + 1 →
        ∀ A B : Finset α, A ⊆ U → B ⊆ U → A.card = n → B.card = n → col A = col B := by
      intro U hUS hUcard A B hAU hBU hAcard hBcard
      have hTcard : (S \ U).card = k * (n + 1) - 1 := by
        rw [Finset.card_sdiff_of_subset hUS, hS, hUcard]
        have e : (k + 1) * (n + 1) = k * (n + 1) + (n + 1) := by ring
        lia
      obtain ⟨F, hFcard, hFsub, hFdisj, c, hFmono⟩ := ih (S \ U) hTcard
      -- No `n`-element subset of `U` can have color `c`.
      have key : ∀ D : Finset α, D ⊆ U → D.card = n → col D = !c := by
        intro D hDU hDcard
        by_contra hDc
        have hDc' : col D = c := by
          revert hDc
          cases c <;> cases col D <;> decide
        have hDnF : D ∉ F := by
          intro hD
          have hDT : D ⊆ S \ U := (hFsub D hD).1
          have hsub : D ⊆ U ∩ (S \ U) := Finset.subset_inter hDU hDT
          have hempty : U ∩ (S \ U) = ∅ :=
            Finset.disjoint_iff_inter_eq_empty.mp Finset.disjoint_sdiff
          rw [hempty] at hsub
          have hDe : D = ∅ := Finset.subset_empty.mp hsub
          rw [hDe, Finset.card_empty] at hDcard
          lia
        apply h
        refine ⟨insert D F, ?_, ?_, ?_, c, ?_⟩
        · rw [Finset.card_insert_of_notMem hDnF]
          lia
        · intro E hE
          rw [Finset.mem_insert] at hE
          rcases hE with rfl | hE
          · exact ⟨hDU.trans hUS, hDcard⟩
          · exact ⟨(hFsub E hE).1.trans Finset.sdiff_subset, (hFsub E hE).2⟩
        · rw [Finset.coe_insert]
          refine Set.PairwiseDisjoint.insert hFdisj fun j hj _ => ?_
          show Disjoint D j
          exact Disjoint.mono hDU (hFsub j hj).1 Finset.disjoint_sdiff
        · intro E hE
          rw [Finset.mem_insert] at hE
          rcases hE with rfl | hE
          · exact hDc'
          · exact hFmono E hE
      have eA := key A hAU hAcard
      have eB := key B hBU hBcard
      rw [eA, eB]
    -- Hence all `n`-element subsets of `S` have the same color, and there are
    -- `k + 1` pairwise disjoint ones: a contradiction.
    have hcardS : (k + 1) * n ≤ S.card := by
      rw [hS]
      have e : (k + 1) * (n + 1) = (k + 1) * n + (k + 1) := by ring
      lia
    obtain ⟨F, hFcard, hFsub, hFdisj⟩ := exists_disjoint_family hn (k + 1) S hcardS
    obtain ⟨A₀, hA₀⟩ : F.Nonempty := by
      rw [← Finset.card_pos, hFcard]
      lia
    have hA₀S : A₀ ⊆ S := (hFsub A₀ hA₀).1
    have hA₀card : A₀.card = n := (hFsub A₀ hA₀).2
    apply h
    refine ⟨F, hFcard.ge, hFsub, hFdisj, col A₀, fun A hA => ?_⟩
    exact color_eq col claim _ A A₀ (hFsub A hA).1 hA₀S (hFsub A hA).2 hA₀card le_rfl

snip end

problem usa2007_p3 (n : ℕ) (hn : 0 < n) {α : Type*} [DecidableEq α] (S : Finset α)
    (hS : S.card = n ^ 2 + n - 1) (col : Finset α → Bool) :
    ∃ F : Finset (Finset α), n ≤ F.card ∧ (∀ A ∈ F, A ⊆ S ∧ A.card = n) ∧
      (F : Set (Finset α)).PairwiseDisjoint id ∧ ∃ b : Bool, ∀ A ∈ F, col A = b := by
  have hS' : S.card = n * (n + 1) - 1 := by
    have e : n * (n + 1) = n ^ 2 + n := by ring
    lia
  exact main col hn n S hS'

end Usa2007P3
