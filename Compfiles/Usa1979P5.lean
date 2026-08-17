/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Ring.Nat
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics] }

/-!
# USA Mathematical Olympiad 1979, Problem 5

X has n members. Given n+1 subsets of X, each with 3 members,
show that we can always find two which have just one member in common.
-/

namespace Usa1979P5

open Finset

snip begin

/-- If two distinct members `s`, `t` of a "good" family (no two sets share exactly
one element) each have three elements and intersect nontrivially, then they share
exactly two elements. -/
theorem card_inter_eq_two_of_good {α : Type*} [DecidableEq α] {S : Finset (Finset α)}
    (hgood : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → (s ∩ t).card ≠ 1)
    {s t : Finset α} (hs : s ∈ S) (ht : t ∈ S) (hne : s ≠ t)
    (hs3 : s.card = 3) (ht3 : t.card = 3) (hpos : 0 < (s ∩ t).card) :
    (s ∩ t).card = 2 := by
  have hle : (s ∩ t).card ≤ 3 := by
    calc (s ∩ t).card ≤ t.card := card_le_card inter_subset_right
      _ = 3 := ht3
  have hne3 : (s ∩ t).card ≠ 3 := by
    intro h3
    have h1 : s ∩ t = t := eq_of_subset_of_card_le inter_subset_right (by lia)
    have h2 : t ⊆ s := h1 ▸ inter_subset_left
    have h3' : t = s := eq_of_subset_of_card_le h2 (by lia)
    exact hne h3'.symm
  have hne1 := hgood s hs t ht hne
  lia

/-- If `u`, `v = {w, x, y}` are members of a "good" family, `w ∈ u ∩ v` and `x ∉ u`,
then `y ∈ u`: otherwise `u ∩ v = {w}` would be a singleton intersection. -/
theorem mem_third_of_inter {α : Type*} [DecidableEq α] {S : Finset (Finset α)}
    (hgood : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → (s ∩ t).card ≠ 1)
    {u v : Finset α} {w x y : α}
    (hu : u ∈ S) (hv : v ∈ S) (hw : w ∈ u ∩ v) (hx : x ∉ u) (hv_eq : v = {w, x, y}) :
    y ∈ u := by
  by_contra hy
  have hxv : x ∈ v := by rw [hv_eq]; simp
  have hne : u ≠ v := by
    intro h
    rw [← h] at hxv
    exact hx hxv
  have hsub : u ∩ v ⊆ {w} := by
    intro z hz
    rw [mem_inter, hv_eq] at hz
    simp only [mem_insert, mem_singleton] at hz
    rcases hz.2 with rfl | rfl | rfl
    · exact mem_singleton_self _
    · exact absurd hz.1 hx
    · exact absurd hz.1 hy
  have heq : u ∩ v = {w} :=
    (eq_of_subset_of_card_le (singleton_subset_iff.mpr hw)
      (by simpa using card_le_card hsub)).symm
  exact hgood u hu v hv hne (by simp [heq])

/-- Double counting of the incidences between `X` and a family of 3-element
subsets of `X`. -/
theorem sum_card_filter_eq_three_mul {α : Type*} [DecidableEq α]
    {X : Finset α} {S : Finset (Finset α)}
    (hsub : ∀ s ∈ S, s ⊆ X) (hcard : ∀ s ∈ S, s.card = 3) :
    ∑ x ∈ X, (S.filter (fun s ↦ x ∈ s)).card = 3 * S.card := by
  have h1 : ∀ x ∈ X, (S.filter (fun s ↦ x ∈ s)).card
      = ∑ s ∈ S, if x ∈ s then 1 else 0 :=
    fun x _ ↦ card_filter _ _
  rw [sum_congr rfl h1, sum_comm]
  have h2 : ∀ s ∈ S, (∑ x ∈ X, if x ∈ s then 1 else 0) = 3 := by
    intro s hs
    rw [← card_filter, filter_mem_eq_inter, inter_eq_right.mpr (hsub s hs)]
    exact hcard s hs
  rw [sum_congr rfl h2, sum_const, smul_eq_mul, mul_comm]

/-- Main step: a "good" family of 3-element subsets of an `n`-element set has at
most `n` members. Proved by strong induction on `n`, following the informal
argument for USAMO 1979 problem 5. -/
theorem card_le_of_good {α : Type*} [DecidableEq α] :
    ∀ n : ℕ, ∀ (X : Finset α) (S : Finset (Finset α)),
    X.card = n → (∀ s ∈ S, s ⊆ X) → (∀ s ∈ S, s.card = 3) →
    (∀ s ∈ S, ∀ t ∈ S, s ≠ t → (s ∩ t).card ≠ 1) → S.card ≤ n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro X S hX hsub hcard hgood
  by_cases hA : ∃ A ∈ X, 3 < (S.filter (fun s ↦ A ∈ s)).card
  · -- Some `A ∈ X` belongs to at least 4 sets of the family.
    obtain ⟨A, hAX, hA4⟩ := hA
    set M := S.filter (fun s ↦ A ∈ s) with hM
    have mem_M : ∀ s : Finset α, s ∈ M ↔ s ∈ S ∧ A ∈ s := by
      intro s; rw [hM]; exact mem_filter
    have hM4 : 3 < M.card := by rw [hM]; exact hA4
    -- Pick `s₀ ∈ M` and write it as `{A, B, C}`.
    have hMpos : M.Nonempty := card_pos.mp (by lia)
    obtain ⟨s₀, hs₀M⟩ := hMpos
    have hs₀S : s₀ ∈ S := ((mem_M _).mp hs₀M).1
    have hAs₀ : A ∈ s₀ := ((mem_M _).mp hs₀M).2
    have hs₀3 : s₀.card = 3 := hcard s₀ hs₀S
    have he2 : (s₀.erase A).card = 2 := by rw [card_erase_of_mem hAs₀, hs₀3]
    obtain ⟨B, C, hBC, hs₀e⟩ := card_eq_two.mp he2
    have hs₀eq : s₀ = {A, B, C} := by rw [← insert_erase hAs₀, hs₀e]
    have hBms₀ : B ∈ s₀.erase A := by rw [hs₀e]; simp
    have hBA : B ≠ A := (mem_erase.mp hBms₀).1
    have hBs₀ : B ∈ s₀ := (mem_erase.mp hBms₀).2
    have hCms₀ : C ∈ s₀.erase A := by rw [hs₀e]; simp
    have hCA : C ≠ A := (mem_erase.mp hCms₀).1
    have hCs₀ : C ∈ s₀ := (mem_erase.mp hCms₀).2
    -- Every other set containing `A` meets `s₀` in exactly two elements, hence
    -- contains `B` or `C`.
    have hinter2 : ∀ t ∈ M.erase s₀, (t ∩ s₀).card = 2 := by
      intro t ht
      have htM : t ∈ M := (mem_erase.mp ht).2
      have hts₀ : t ≠ s₀ := (mem_erase.mp ht).1
      have htS : t ∈ S := ((mem_M _).mp htM).1
      have hAt : A ∈ t := ((mem_M _).mp htM).2
      exact card_inter_eq_two_of_good hgood htS hs₀S hts₀ (hcard t htS) hs₀3
        (card_pos.mpr ⟨A, mem_inter.mpr ⟨hAt, hAs₀⟩⟩)
    have hBC_of_mem : ∀ t ∈ M.erase s₀, B ∈ t ∨ C ∈ t := by
      intro t ht
      have h2 := hinter2 t ht
      have hAint : A ∈ t ∩ s₀ :=
        mem_inter.mpr ⟨((mem_M _).mp (mem_erase.mp ht).2).2, hAs₀⟩
      have hss : {A} ⊂ t ∩ s₀ := by
        rw [Finset.ssubset_iff_subset_ne]
        refine ⟨singleton_subset_iff.mpr hAint, fun h ↦ ?_⟩
        rw [← h] at h2
        simp at h2
      obtain ⟨x, hxint, hxA⟩ := exists_of_ssubset hss
      have hxs₀ : x ∈ s₀ := (mem_inter.mp hxint).2
      have hxt : x ∈ t := (mem_inter.mp hxint).1
      have hxne : x ≠ A := fun h ↦ hxA (mem_singleton.mpr h)
      rw [hs₀eq] at hxs₀
      simp only [mem_insert, mem_singleton] at hxs₀
      rcases hxs₀ with rfl | rfl | rfl
      · exact absurd rfl hxne
      · exact Or.inl hxt
      · exact Or.inr hxt
    -- Hence one of `B`, `C` (say `P`, the other being `Q`) belongs to at least
    -- two sets of `M` different from `s₀`.
    have he3 : 3 ≤ (M.erase s₀).card := by rw [card_erase_of_mem hs₀M]; lia
    have hsub2 : M.erase s₀ ⊆ ((M.filter (fun s ↦ B ∈ s)).erase s₀)
        ∪ ((M.filter (fun s ↦ C ∈ s)).erase s₀) := by
      intro t ht
      rcases hBC_of_mem t ht with hB | hC
      · exact mem_union_left _ (mem_erase.mpr ⟨(mem_erase.mp ht).1,
          mem_filter.mpr ⟨(mem_erase.mp ht).2, hB⟩⟩)
      · exact mem_union_right _ (mem_erase.mpr ⟨(mem_erase.mp ht).1,
          mem_filter.mpr ⟨(mem_erase.mp ht).2, hC⟩⟩)
    have h33 : 3 ≤ ((M.filter (fun s ↦ B ∈ s)).erase s₀).card
        + ((M.filter (fun s ↦ C ∈ s)).erase s₀).card :=
      le_trans (le_trans he3 (card_le_card hsub2)) (card_union_le _ _)
    have hcases : 2 ≤ ((M.filter (fun s ↦ B ∈ s)).erase s₀).card
        ∨ 2 ≤ ((M.filter (fun s ↦ C ∈ s)).erase s₀).card := by lia
    -- The rest of the argument only uses the popular element `P`, the spare
    -- element `Q` of `s₀ = {A, P, Q}`, and two sets containing `A` and `P`.
    have extract : ∀ P Q : α, A ≠ P → A ≠ Q → P ≠ Q → s₀ = {A, P, Q} →
        2 ≤ ((M.filter (fun s ↦ P ∈ s)).erase s₀).card → S.card ≤ n := by
      intro P Q hAP hAQ hPQ hs₀PQ h2
      obtain ⟨t₁, ht₁, t₂, ht₂, ht₁t₂⟩ := one_lt_card.mp (by lia :
        1 < ((M.filter (fun s ↦ P ∈ s)).erase s₀).card)
      -- Unpack `t₁` and `t₂`.
      have ht₁s₀ : t₁ ≠ s₀ := (mem_erase.mp ht₁).1
      have ht₁M : t₁ ∈ M := (mem_filter.mp (mem_erase.mp ht₁).2).1
      have hPt₁ : P ∈ t₁ := (mem_filter.mp (mem_erase.mp ht₁).2).2
      have ht₁S : t₁ ∈ S := ((mem_M _).mp ht₁M).1
      have hAt₁ : A ∈ t₁ := ((mem_M _).mp ht₁M).2
      have ht₁3 : t₁.card = 3 := hcard t₁ ht₁S
      have ht₂s₀ : t₂ ≠ s₀ := (mem_erase.mp ht₂).1
      have ht₂M : t₂ ∈ M := (mem_filter.mp (mem_erase.mp ht₂).2).1
      have hPt₂ : P ∈ t₂ := (mem_filter.mp (mem_erase.mp ht₂).2).2
      have ht₂S : t₂ ∈ S := ((mem_M _).mp ht₂M).1
      have hAt₂ : A ∈ t₂ := ((mem_M _).mp ht₂M).2
      have ht₂3 : t₂.card = 3 := hcard t₂ ht₂S
      have ht₁Me : t₁ ∈ M.erase s₀ := mem_erase.mpr ⟨ht₁s₀, ht₁M⟩
      have ht₂Me : t₂ ∈ M.erase s₀ := mem_erase.mpr ⟨ht₂s₀, ht₂M⟩
      -- Write `t₁ = {A, P, D}` and `t₂ = {A, P, E}`.
      have hD1 : ((t₁.erase A).erase P).card = 1 := by
        rw [card_erase_of_mem (mem_erase.mpr ⟨hAP.symm, hPt₁⟩),
          card_erase_of_mem hAt₁, ht₁3]
      obtain ⟨D, hD⟩ := card_eq_one.mp hD1
      have ht₁eq : t₁ = {A, P, D} := by
        rw [← insert_erase hAt₁,
          ← insert_erase (mem_erase.mpr ⟨hAP.symm, hPt₁⟩), hD]
      have hDe : D ∈ (t₁.erase A).erase P := by rw [hD]; exact mem_singleton_self D
      have hDP : D ≠ P := (mem_erase.mp hDe).1
      have hDA : D ≠ A := (mem_erase.mp (mem_erase.mp hDe).2).1
      have hDt₁ : D ∈ t₁ := (mem_erase.mp (mem_erase.mp hDe).2).2
      have hE1 : ((t₂.erase A).erase P).card = 1 := by
        rw [card_erase_of_mem (mem_erase.mpr ⟨hAP.symm, hPt₂⟩),
          card_erase_of_mem hAt₂, ht₂3]
      obtain ⟨E, hE⟩ := card_eq_one.mp hE1
      have ht₂eq : t₂ = {A, P, E} := by
        rw [← insert_erase hAt₂,
          ← insert_erase (mem_erase.mpr ⟨hAP.symm, hPt₂⟩), hE]
      have hEe : E ∈ (t₂.erase A).erase P := by rw [hE]; exact mem_singleton_self E
      have hEP : E ≠ P := (mem_erase.mp hEe).1
      have hEA : E ≠ A := (mem_erase.mp (mem_erase.mp hEe).2).1
      have hEt₂ : E ∈ t₂ := (mem_erase.mp (mem_erase.mp hEe).2).2
      -- `D, E ∉ s₀` and `D ≠ E`, so `A, P, Q, D, E` are pairwise distinct.
      have hDQ : D ≠ Q := by
        intro h
        have hAint : A ∈ t₁ ∩ s₀ := mem_inter.mpr ⟨hAt₁, hAs₀⟩
        have hPint : P ∈ t₁ ∩ s₀ :=
          mem_inter.mpr ⟨hPt₁, by rw [hs₀PQ]; simp⟩
        have hQint : Q ∈ t₁ ∩ s₀ :=
          mem_inter.mpr ⟨h ▸ hDt₁, by rw [hs₀PQ]; simp⟩
        have hsub3 : ({A, P, Q} : Finset α) ⊆ t₁ ∩ s₀ := by
          intro z hz
          simp only [mem_insert, mem_singleton] at hz
          rcases hz with rfl | rfl | rfl <;> assumption
        have h3 : ({A, P, Q} : Finset α).card = 3 := by
          rw [card_insert_of_notMem (by simp [hAP, hAQ]),
            card_insert_of_notMem (by simp [hPQ]), card_singleton]
        have hle3 : 3 ≤ (t₁ ∩ s₀).card := h3 ▸ card_le_card hsub3
        have h2' := hinter2 t₁ ht₁Me
        lia
      have hEQ : E ≠ Q := by
        intro h
        have hAint : A ∈ t₂ ∩ s₀ := mem_inter.mpr ⟨hAt₂, hAs₀⟩
        have hPint : P ∈ t₂ ∩ s₀ :=
          mem_inter.mpr ⟨hPt₂, by rw [hs₀PQ]; simp⟩
        have hQint : Q ∈ t₂ ∩ s₀ :=
          mem_inter.mpr ⟨h ▸ hEt₂, by rw [hs₀PQ]; simp⟩
        have hsub3 : ({A, P, Q} : Finset α) ⊆ t₂ ∩ s₀ := by
          intro z hz
          simp only [mem_insert, mem_singleton] at hz
          rcases hz with rfl | rfl | rfl <;> assumption
        have h3 : ({A, P, Q} : Finset α).card = 3 := by
          rw [card_insert_of_notMem (by simp [hAP, hAQ]),
            card_insert_of_notMem (by simp [hPQ]), card_singleton]
        have hle3 : 3 ≤ (t₂ ∩ s₀).card := h3 ▸ card_le_card hsub3
        have h2' := hinter2 t₂ ht₂Me
        lia
      have hDE : D ≠ E := fun h ↦ ht₁t₂ (by rw [ht₁eq, ht₂eq, h])
      -- Key claim 1: every set of the family containing `A` contains `P`.
      have hstep1 : ∀ u ∈ S, A ∈ u → P ∈ u := by
        intro u huS hAu
        by_contra hPu
        have hQu : Q ∈ u := mem_third_of_inter hgood huS hs₀S
          (mem_inter.mpr ⟨hAu, hAs₀⟩) hPu hs₀PQ
        have hDu : D ∈ u := mem_third_of_inter hgood huS ht₁S
          (mem_inter.mpr ⟨hAu, hAt₁⟩) hPu ht₁eq
        have hEu : E ∈ u := mem_third_of_inter hgood huS ht₂S
          (mem_inter.mpr ⟨hAu, hAt₂⟩) hPu ht₂eq
        have hsub4 : ({A, Q, D, E} : Finset α) ⊆ u := by
          intro z hz
          simp only [mem_insert, mem_singleton] at hz
          rcases hz with rfl | rfl | rfl | rfl <;> assumption
        have h4 : ({A, Q, D, E} : Finset α).card = 4 := by
          rw [card_insert_of_notMem (by simp [hAQ, hDA.symm, hEA.symm]),
            card_insert_of_notMem (by simp [hDQ.symm, hEQ.symm]),
            card_insert_of_notMem (by simp [hDE]), card_singleton]
        have hle4 := card_le_card hsub4
        rw [h4, hcard u huS] at hle4
        lia
      -- Key claim 2: every set of the family containing `P` contains `A`.
      have hstep2 : ∀ u ∈ S, P ∈ u → A ∈ u := by
        intro u huS hPu
        by_contra hAu
        have hPs₀ : P ∈ s₀ := by rw [hs₀PQ]; simp
        have hQu : Q ∈ u := mem_third_of_inter hgood huS hs₀S
          (mem_inter.mpr ⟨hPu, hPs₀⟩) hAu (by rw [hs₀PQ, insert_comm])
        have hDu : D ∈ u := mem_third_of_inter hgood huS ht₁S
          (mem_inter.mpr ⟨hPu, hPt₁⟩) hAu (by rw [ht₁eq, insert_comm])
        have hEu : E ∈ u := mem_third_of_inter hgood huS ht₂S
          (mem_inter.mpr ⟨hPu, hPt₂⟩) hAu (by rw [ht₂eq, insert_comm])
        have hsub4 : ({P, Q, D, E} : Finset α) ⊆ u := by
          intro z hz
          simp only [mem_insert, mem_singleton] at hz
          rcases hz with rfl | rfl | rfl | rfl <;> assumption
        have h4 : ({P, Q, D, E} : Finset α).card = 4 := by
          rw [card_insert_of_notMem (by simp [hPQ, hDP.symm, hEP.symm]),
            card_insert_of_notMem (by simp [hDQ.symm, hEQ.symm]),
            card_insert_of_notMem (by simp [hDE]), card_singleton]
        have hle4 := card_le_card hsub4
        rw [h4, hcard u huS] at hle4
        lia
      -- `M` has at least three members.
      have hM3 : 3 ≤ M.card := Nat.le_of_lt hA4
      -- The third elements `K` of the sets `{A, P, K} ∈ M`.
      set Ks := M.biUnion (fun s ↦ (s.erase A).erase P) with hKs
      have mem_Ks : ∀ x : α, x ∈ Ks ↔ ∃ s ∈ M, x ∈ (s.erase A).erase P := by
        intro x; rw [hKs]; exact mem_biUnion
      have hK1 : ∀ s ∈ M, ((s.erase A).erase P).card = 1 := by
        intro s hsM
        have hsS : s ∈ S := ((mem_M _).mp hsM).1
        have hAs : A ∈ s := ((mem_M _).mp hsM).2
        have hPs : P ∈ s := hstep1 s hsS hAs
        rw [card_erase_of_mem (mem_erase.mpr ⟨hAP.symm, hPs⟩),
          card_erase_of_mem hAs, hcard s hsS]
      have hdisj : (M : Set (Finset α)).PairwiseDisjoint
          (fun s ↦ (s.erase A).erase P) := by
        intro s₁ hs₁ s₂ hs₂ hne12
        refine Finset.disjoint_left.mpr ?_
        intro K hK1 hK2
        have hKP : K ≠ P := (mem_erase.mp hK1).1
        have hKA : K ≠ A := (mem_erase.mp (mem_erase.mp hK1).2).1
        have hKs₁ : K ∈ s₁ := (mem_erase.mp (mem_erase.mp hK1).2).2
        have hKs₂ : K ∈ s₂ := (mem_erase.mp (mem_erase.mp hK2).2).2
        have hAs₁ : A ∈ s₁ := ((mem_M _).mp hs₁).2
        have hPs₁ : P ∈ s₁ := hstep1 s₁ ((mem_M _).mp hs₁).1 hAs₁
        have hAs₂ : A ∈ s₂ := ((mem_M _).mp hs₂).2
        have hPs₂ : P ∈ s₂ := hstep1 s₂ ((mem_M _).mp hs₂).1 hAs₂
        have hsub3 : ({A, P, K} : Finset α) ⊆ s₁ ∩ s₂ := by
          intro z hz
          simp only [mem_insert, mem_singleton] at hz
          rw [mem_inter]
          rcases hz with rfl | rfl | rfl
          · exact ⟨hAs₁, hAs₂⟩
          · exact ⟨hPs₁, hPs₂⟩
          · exact ⟨hKs₁, hKs₂⟩
        have hcard3 : ({A, P, K} : Finset α).card = 3 := by
          rw [card_insert_of_notMem (by simp [hAP, hKA.symm]),
            card_insert_of_notMem (by simp [hKP.symm]), card_singleton]
        have hle3 : 3 ≤ (s₁ ∩ s₂).card := hcard3 ▸ card_le_card hsub3
        have hs₁3 : s₁.card = 3 := hcard s₁ ((mem_M _).mp hs₁).1
        have hs₂3 : s₂.card = 3 := hcard s₂ ((mem_M _).mp hs₂).1
        have heq1 : s₁ ∩ s₂ = s₁ := eq_of_subset_of_card_le inter_subset_left (by lia)
        have hs₁s₂ : s₁ ⊆ s₂ := by rw [← heq1]; exact inter_subset_right
        exact hne12 (eq_of_subset_of_card_le hs₁s₂ (by lia))
      have hKsM : Ks.card = M.card := by
        rw [hKs, card_biUnion hdisj, sum_congr rfl hK1, sum_const, smul_eq_mul,
          mul_one]
      -- Every `K ∈ Ks` belongs to no set of the family outside `M`.
      have hKnot : ∀ u ∈ S, u ∉ M → ∀ K ∈ Ks, K ∉ u := by
        intro u huS huM K hKKs
        rw [mem_Ks] at hKKs
        obtain ⟨v, hvM, hKv⟩ := hKKs
        have hvS : v ∈ S := ((mem_M _).mp hvM).1
        have hAv : A ∈ v := ((mem_M _).mp hvM).2
        have hPv : P ∈ v := hstep1 v hvS hAv
        have hKv2 : K ∈ v := (mem_erase.mp (mem_erase.mp hKv).2).2
        have hKA : K ≠ A := (mem_erase.mp (mem_erase.mp hKv).2).1
        have hKP : K ≠ P := (mem_erase.mp hKv).1
        intro hKu
        have hAu : A ∉ u := fun h ↦ huM ((mem_M _).mpr ⟨huS, h⟩)
        have hPu : P ∉ u := fun h ↦ hAu (hstep2 u huS h)
        have hsub1 : u ∩ v ⊆ {K} := by
          intro z hz
          rw [mem_inter] at hz
          have hzA : z ≠ A := fun h ↦ hAu (h ▸ hz.1)
          have hzP : z ≠ P := fun h ↦ hPu (h ▸ hz.1)
          have hzv : z ∈ (v.erase A).erase P :=
            mem_erase.mpr ⟨hzP, mem_erase.mpr ⟨hzA, hz.2⟩⟩
          obtain ⟨w, hw⟩ := card_eq_one.mp (hK1 v hvM)
          have hKw : K = w := by rw [hw] at hKv; exact mem_singleton.mp hKv
          have hzw : z = w := by rw [hw] at hzv; exact mem_singleton.mp hzv
          rw [mem_singleton]
          exact hzw.trans hKw.symm
        have heq : u ∩ v = {K} :=
          (eq_of_subset_of_card_le
            (singleton_subset_iff.mpr (mem_inter.mpr ⟨hKu, hKv2⟩))
            (by simpa using card_le_card hsub1)).symm
        have huv : u ≠ v := fun h ↦ huM (h ▸ hvM)
        exact hgood u huS v hvS huv (by simp [heq])
      -- The set of elements to avoid: `A`, `P` and all the `K`s.
      set avoid := insert A (insert P Ks) with havoid
      have hAnotin : A ∉ insert P Ks := by
        rw [mem_insert]
        push Not
        refine ⟨hAP, fun hAKs ↦ ?_⟩
        rw [mem_Ks] at hAKs
        obtain ⟨s, hsM, hAs⟩ := hAKs
        exact (mem_erase.mp (mem_erase.mp hAs).2).1 rfl
      have hPnotin : P ∉ Ks := by
        intro hPKs
        rw [mem_Ks] at hPKs
        obtain ⟨s, hsM, hPs⟩ := hPKs
        exact (mem_erase.mp hPs).1 rfl
      have havoidcard : avoid.card = M.card + 2 := by
        rw [havoid, card_insert_of_notMem hAnotin, card_insert_of_notMem hPnotin,
          hKsM]
      have havoidX : avoid ⊆ X := by
        intro z hz
        rw [havoid, mem_insert] at hz
        rcases hz with rfl | hz
        · exact hAX
        · rw [mem_insert] at hz
          rcases hz with rfl | hz
          · exact hsub s₀ hs₀S (by rw [hs₀PQ]; simp)
          · rw [mem_Ks] at hz
            obtain ⟨s, hsM, hzs⟩ := hz
            exact hsub s ((mem_M _).mp hsM).1 (mem_erase.mp (mem_erase.mp hzs).2).2
      -- The remaining elements `T = X \ avoid` have `n - (|M| + 2) < n` members.
      set T := X \ avoid with hT
      have hTcard : T.card = n - avoid.card := by
        rw [hT, card_sdiff, inter_eq_left.mpr havoidX, hX]
      have hTlt : T.card < n := by
        have h1 : 0 < avoid.card := by lia
        have h2 : avoid.card ≤ n := hX ▸ card_le_card havoidX
        lia
      -- Every set of the family avoiding `A` is a 3-subset of `T`.
      set S' := S.filter (fun s ↦ A ∉ s) with hS'
      have hS'sub : ∀ s ∈ S', s ⊆ T := by
        intro s hsS' x hx
        have hsS : s ∈ S := mem_of_mem_filter _ hsS'
        have hAs : A ∉ s := (mem_filter.mp hsS').2
        rw [hT, mem_sdiff]
        refine ⟨hsub s hsS hx, fun hxa ↦ ?_⟩
        rw [havoid, mem_insert] at hxa
        rcases hxa with rfl | hxa
        · exact hAs hx
        · rw [mem_insert] at hxa
          rcases hxa with rfl | hxKs
          · exact hAs (hstep2 s hsS hx)
          · have hsM : s ∉ M := fun h ↦ hAs (((mem_M _).mp h).2)
            exact hKnot s hsS hsM x hxKs hx
      have hS'card : S'.card ≤ T.card := by
        have hsub3' : ∀ s ∈ S', s.card = 3 := fun s hs ↦ hcard s (mem_of_mem_filter _ hs)
        have hgood' : ∀ s ∈ S', ∀ t ∈ S', s ≠ t → (s ∩ t).card ≠ 1 :=
          fun s hs t ht ↦ hgood s (mem_of_mem_filter _ hs) t (mem_of_mem_filter _ ht)
        exact ih T.card hTlt T S' rfl hS'sub hsub3' hgood'
      have hScard : S.card = M.card + S'.card := by
        rw [hM, hS']
        exact (card_filter_add_card_filter_not (fun s ↦ A ∈ s) (s := S)).symm
      have h2n : avoid.card ≤ n := hX ▸ card_le_card havoidX
      lia
    rcases hcases with hB2 | hC2
    · exact extract B C hBA.symm hCA.symm hBC hs₀eq hB2
    · exact extract C B hCA.symm hBA.symm hBC.symm (by rw [hs₀eq, pair_comm]) hC2
  · -- Otherwise every element of `X` is in at most 3 sets, and double counting
    -- gives the bound directly.
    push Not at hA
    have hle : ∑ x ∈ X, (S.filter (fun s ↦ x ∈ s)).card ≤ ∑ _x ∈ X, 3 :=
      sum_le_sum hA
    rw [sum_card_filter_eq_three_mul hsub hcard, sum_const, smul_eq_mul, hX] at hle
    lia

snip end

problem usa1979_p5 {α : Type*} [DecidableEq α] (n : ℕ) (X : Finset α) (hX : X.card = n)
    (S : Finset (Finset α)) (hS : S.card = n + 1) (hsub : ∀ s ∈ S, s ⊆ X)
    (hcard : ∀ s ∈ S, s.card = 3) :
    ∃ s ∈ S, ∃ t ∈ S, s ≠ t ∧ (s ∩ t).card = 1 := by
  by_contra h
  push Not at h
  have hle := card_le_of_good n X S hX hsub hcard h
  lia

end Usa1979P5
