/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Data.Int.ConditionallyCompleteOrder
public import Mathlib.Data.Int.Star
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics] }

/-!
# USA Mathematical Olympiad 2011, Problem 6

Let A be a set with |A| = 225, meaning that A has 225 elements. Suppose further
that there are eleven subsets A₁, A₂, ..., A₁₁ of A such that |Aᵢ| = 45 for
1 ≤ i ≤ 11 and |Aᵢ ∩ Aⱼ| = 9 for 1 ≤ i < j ≤ 11. Prove that
|A₁ ∪ A₂ ∪ ··· ∪ A₁₁| ≥ 165, and give an example for which equality holds.
-/

namespace Usa2011P6

snip begin

-- We follow the double-counting plus Cauchy–Schwarz argument from
-- https://web.evanchen.cc/exams/USAMO-2011-notes.pdf.

/-- Double counting: for a predicate `p` on `t × u`, the sum over `a ∈ u` of the number
of indices `i ∈ t` satisfying `p i a` equals the sum over `i ∈ t` of the number of
elements `a ∈ u` satisfying `p i a`. -/
lemma sum_card_filter_comm {ι α : Type*} {t : Finset ι} {u : Finset α}
    (p : ι → α → Prop) [∀ i a, Decidable (p i a)] :
    ∑ a ∈ u, (t.filter fun i ↦ p i a).card = ∑ i ∈ t, (u.filter fun a ↦ p i a).card := by
  simp_rw [Finset.card_filter]
  exact Finset.sum_comm

/-- There are exactly 45 three-element subsets of an 11-element set containing a given
element `i`: erasing `i` puts them in bijection with the 2-element subsets of the
remaining 10 elements, and `Nat.choose 10 2 = 45`. -/
lemma card_powersetCard_filter_mem (i : Fin 11) :
    (((Finset.univ : Finset (Fin 11)).powersetCard 3).filter fun T ↦ i ∈ T).card = 45 := by
  have hbij : (((Finset.univ : Finset (Fin 11)).powersetCard 3).filter fun T ↦ i ∈ T).card
      = ((Finset.univ.erase i).powersetCard 2).card := by
    refine Finset.card_bij' (fun T _ ↦ T.erase i) (fun S _ ↦ insert i S)
      (fun T hT ↦ ?_) (fun S hS ↦ ?_) (fun T hT ↦ ?_) (fun S hS ↦ ?_)
    · show T.erase i ∈ (Finset.univ.erase i).powersetCard 2
      rw [Finset.mem_filter, Finset.mem_powersetCard] at hT
      obtain ⟨⟨hTsub, hTcard⟩, hiT⟩ := hT
      rw [Finset.mem_powersetCard]
      exact ⟨Finset.erase_subset_erase i hTsub, by rw [Finset.card_erase_of_mem hiT, hTcard]⟩
    · show insert i S ∈ _
      rw [Finset.mem_powersetCard] at hS
      obtain ⟨hSsub, hScard⟩ := hS
      have hiS : i ∉ S := fun hi ↦ Finset.notMem_erase i Finset.univ (hSsub hi)
      rw [Finset.mem_filter, Finset.mem_powersetCard]
      exact ⟨⟨Finset.insert_subset (Finset.mem_univ i) (hSsub.trans (Finset.erase_subset _ _)),
          by rw [Finset.card_insert_of_notMem hiS, hScard]⟩,
        Finset.mem_insert_self i S⟩
    · show insert i (T.erase i) = T
      rw [Finset.mem_filter] at hT
      exact Finset.insert_erase hT.2
    · show (insert i S).erase i = S
      rw [Finset.mem_powersetCard] at hS
      exact Finset.erase_insert (fun hi ↦ Finset.notMem_erase i Finset.univ (hS.1 hi))
  rw [hbij, Finset.card_powersetCard, Finset.card_erase_of_mem (Finset.mem_univ i),
    Finset.card_univ, Fintype.card_fin]
  decide

/-- There are exactly 9 three-element subsets of an 11-element set containing two given
distinct elements `i` and `j`: erasing both puts them in bijection with the 1-element
subsets of the remaining 9 elements, and `Nat.choose 9 1 = 9`. -/
lemma card_powersetCard_filter_mem₂ {i j : Fin 11} (hij : i ≠ j) :
    (((Finset.univ : Finset (Fin 11)).powersetCard 3).filter fun T ↦ i ∈ T ∧ j ∈ T).card
      = 9 := by
  have hbij : (((Finset.univ : Finset (Fin 11)).powersetCard 3).filter
        fun T ↦ i ∈ T ∧ j ∈ T).card
      = (((Finset.univ.erase i).erase j).powersetCard 1).card := by
    refine Finset.card_bij' (fun T _ ↦ (T.erase i).erase j) (fun S _ ↦ insert i (insert j S))
      (fun T hT ↦ ?_) (fun S hS ↦ ?_) (fun T hT ↦ ?_) (fun S hS ↦ ?_)
    · show (T.erase i).erase j ∈ ((Finset.univ.erase i).erase j).powersetCard 1
      rw [Finset.mem_filter, Finset.mem_powersetCard] at hT
      obtain ⟨⟨hTsub, hTcard⟩, hiT, hjT⟩ := hT
      have hjTi : j ∈ T.erase i := Finset.mem_erase.mpr ⟨hij.symm, hjT⟩
      rw [Finset.mem_powersetCard]
      exact ⟨Finset.erase_subset_erase j (Finset.erase_subset_erase i hTsub),
        by rw [Finset.card_erase_of_mem hjTi, Finset.card_erase_of_mem hiT, hTcard]⟩
    · show insert i (insert j S) ∈ _
      rw [Finset.mem_powersetCard] at hS
      obtain ⟨hSsub, hScard⟩ := hS
      have hiS : i ∉ S := fun hi ↦
        Finset.notMem_erase i Finset.univ (Finset.erase_subset _ _ (hSsub hi))
      have hjS : j ∉ S := fun hj ↦ Finset.notMem_erase j _ (hSsub hj)
      have hijS : i ∉ insert j S := fun h ↦ (Finset.mem_insert.mp h).elim (fun e ↦ hij e) hiS
      have hjiS : j ∉ insert i S := fun h ↦ (Finset.mem_insert.mp h).elim (fun e ↦ hij e.symm)
        hjS
      rw [Finset.mem_filter, Finset.mem_powersetCard]
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
      · exact Finset.subset_univ _
      · rw [Finset.card_insert_of_notMem hijS, Finset.card_insert_of_notMem hjS, hScard]
      · exact Finset.mem_insert_self i _
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_self j S)
    · show insert i (insert j ((T.erase i).erase j)) = T
      rw [Finset.mem_filter] at hT
      have hjTi : j ∈ T.erase i := Finset.mem_erase.mpr ⟨hij.symm, hT.2.2⟩
      rw [Finset.insert_erase hjTi, Finset.insert_erase hT.2.1]
    · show ((insert i (insert j S)).erase i).erase j = S
      rw [Finset.mem_powersetCard] at hS
      have hiS : i ∉ S := fun hi ↦
        Finset.notMem_erase i Finset.univ (Finset.erase_subset _ _ (hS.1 hi))
      have hjS : j ∉ S := fun hj ↦ Finset.notMem_erase j _ (hS.1 hj)
      have hijS : i ∉ insert j S := fun h ↦ (Finset.mem_insert.mp h).elim (fun e ↦ hij e) hiS
      rw [Finset.erase_insert hijS, Finset.erase_insert hjS]
  rw [hbij, Finset.card_powersetCard,
    Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩),
    Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
  decide

/-- The sum of the multiplicities of the elements of the union equals the sum of the
sizes of the eleven sets, `11 * 45 = 495`. -/
lemma sum_multiplicity {α : Type*} [DecidableEq α] (As : Fin 11 → Finset α)
    (hcard : ∀ i, (As i).card = 45) :
    ∑ a ∈ Finset.univ.biUnion As, (Finset.univ.filter fun i ↦ a ∈ As i).card = 495 := by
  set U := Finset.univ.biUnion As with hU
  have hsubU : ∀ i, As i ⊆ U := fun i a ha ↦
    Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, ha⟩
  have hfilter_self : ∀ i : Fin 11, U.filter (fun a ↦ a ∈ As i) = As i := by
    intro i
    ext a
    simp only [Finset.mem_filter]
    exact ⟨fun ⟨_, h⟩ ↦ h, fun h ↦ ⟨hsubU i h, h⟩⟩
  calc ∑ a ∈ U, (Finset.univ.filter fun i ↦ a ∈ As i).card
      = ∑ i : Fin 11, (U.filter fun a ↦ a ∈ As i).card :=
        sum_card_filter_comm fun i a ↦ a ∈ As i
    _ = ∑ i : Fin 11, (As i).card :=
        Finset.sum_congr rfl fun i _ ↦ by rw [hfilter_self i]
    _ = 495 := by
        rw [Finset.sum_const_nat fun i _ ↦ hcard i, Finset.card_univ, Fintype.card_fin]

/-- The sum of the intersection sizes over all ordered pairs of indices equals
`11 * 45 + 11 * 10 * 9 = 1485`. -/
lemma sum_inter_card {α : Type*} [DecidableEq α] (As : Fin 11 → Finset α)
    (hcard : ∀ i, (As i).card = 45)
    (hinter : ∀ i j, i ≠ j → (As i ∩ As j).card = 9) :
    ∑ ij ∈ (Finset.univ : Finset (Fin 11)) ×ˢ Finset.univ, (As ij.1 ∩ As ij.2).card
      = 1485 := by
  -- The sum over the diagonal is `11 * 45` and the sum over the off-diagonal is
  -- `11 * 10 * 9`.
  have hdiag : ∑ ij ∈ (Finset.univ : Finset (Fin 11)).diag, (As ij.1 ∩ As ij.2).card
      = 495 := by
    have h : ∀ ij ∈ (Finset.univ : Finset (Fin 11)).diag, (As ij.1 ∩ As ij.2).card = 45 := by
      intro ij hij
      rw [Finset.mem_diag] at hij
      rw [← hij.2, Finset.inter_self, hcard]
    rw [Finset.sum_const_nat h, Finset.diag_card, Finset.card_univ, Fintype.card_fin]
  have hoff : ∑ ij ∈ (Finset.univ : Finset (Fin 11)).offDiag, (As ij.1 ∩ As ij.2).card
      = 990 := by
    have h : ∀ ij ∈ (Finset.univ : Finset (Fin 11)).offDiag, (As ij.1 ∩ As ij.2).card = 9 :=
      fun ij hij ↦ hinter ij.1 ij.2 (Finset.mem_offDiag.mp hij).2.2
    rw [Finset.sum_const_nat h, Finset.offDiag_card, Finset.card_univ, Fintype.card_fin]
  rw [← Finset.diag_union_offDiag, Finset.sum_union (Finset.disjoint_diag_offDiag _),
    hdiag, hoff]

/-- The sum of the squares of the multiplicities equals the sum of the intersection
sizes over all ordered pairs of indices. -/
lemma sum_sq_multiplicity_eq {α : Type*} [DecidableEq α] (As : Fin 11 → Finset α) :
    ∑ a ∈ Finset.univ.biUnion As, (Finset.univ.filter fun i ↦ a ∈ As i).card ^ 2
      = ∑ ij ∈ (Finset.univ : Finset (Fin 11)) ×ˢ Finset.univ,
          (As ij.1 ∩ As ij.2).card := by
  set U := Finset.univ.biUnion As with hU
  have hfilter_inter : ∀ ij : Fin 11 × Fin 11,
      U.filter (fun a ↦ a ∈ As ij.1 ∧ a ∈ As ij.2) = As ij.1 ∩ As ij.2 := by
    intro ij
    ext a
    simp only [Finset.mem_filter, Finset.mem_inter]
    exact ⟨fun ⟨_, h1, h2⟩ ↦ ⟨h1, h2⟩,
      fun ⟨h1, h2⟩ ↦ ⟨Finset.mem_biUnion.mpr ⟨ij.1, Finset.mem_univ _, h1⟩, h1, h2⟩⟩
  have h1 : ∀ a ∈ U, (Finset.univ.filter fun i ↦ a ∈ As i).card ^ 2
      = (((Finset.univ : Finset (Fin 11)) ×ˢ Finset.univ).filter fun ij ↦
          a ∈ As ij.1 ∧ a ∈ As ij.2).card := by
    intro a _
    have hprod : (Finset.univ.filter fun i ↦ a ∈ As i) ×ˢ (Finset.univ.filter fun i ↦ a ∈ As i)
        = ((Finset.univ : Finset (Fin 11)) ×ˢ Finset.univ).filter fun ij ↦
            a ∈ As ij.1 ∧ a ∈ As ij.2 := by
      ext ⟨i, j⟩
      simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [pow_two, ← Finset.card_product, hprod]
  calc ∑ a ∈ U, (Finset.univ.filter fun i ↦ a ∈ As i).card ^ 2
      = ∑ a ∈ U, (((Finset.univ : Finset (Fin 11)) ×ˢ Finset.univ).filter fun ij ↦
            a ∈ As ij.1 ∧ a ∈ As ij.2).card := Finset.sum_congr rfl h1
    _ = ∑ ij ∈ (Finset.univ : Finset (Fin 11)) ×ˢ Finset.univ,
          (U.filter fun a ↦ a ∈ As ij.1 ∧ a ∈ As ij.2).card :=
        sum_card_filter_comm fun (ij : Fin 11 × Fin 11) (a : α) ↦ a ∈ As ij.1 ∧ a ∈ As ij.2
    _ = ∑ ij ∈ (Finset.univ : Finset (Fin 11)) ×ˢ Finset.univ, (As ij.1 ∩ As ij.2).card :=
        Finset.sum_congr rfl fun ij _ ↦ by rw [hfilter_inter ij]

/-- The sum of the squares of the multiplicities equals
`11 * 45 + 11 * 10 * 9 = 1485`. -/
lemma sum_sq_multiplicity {α : Type*} [DecidableEq α] (As : Fin 11 → Finset α)
    (hcard : ∀ i, (As i).card = 45)
    (hinter : ∀ i j, i ≠ j → (As i ∩ As j).card = 9) :
    ∑ a ∈ Finset.univ.biUnion As, (Finset.univ.filter fun i ↦ a ∈ As i).card ^ 2
      = 1485 :=
  (sum_sq_multiplicity_eq As).trans (sum_inter_card As hcard hinter)

snip end

problem usa2011_p6 {α : Type*} [DecidableEq α] (A : Finset α) (As : Fin 11 → Finset α)
    (_hA : A.card = 225) (_hsub : ∀ i, As i ⊆ A)
    (hcard : ∀ i, (As i).card = 45)
    (hinter : ∀ i j, i ≠ j → (As i ∩ As j).card = 9) :
    165 ≤ (Finset.univ.biUnion As).card := by
  -- Cauchy–Schwarz: `(∑ x)² ≤ n ∑ x²`.
  have c1 : (∑ a ∈ Finset.univ.biUnion As,
      ((Finset.univ.filter fun i ↦ a ∈ As i).card : ℤ)) = 495 := by
    exact_mod_cast sum_multiplicity As hcard
  have c2 : (∑ a ∈ Finset.univ.biUnion As,
      ((Finset.univ.filter fun i ↦ a ∈ As i).card : ℤ) ^ 2) = 1485 := by
    exact_mod_cast sum_sq_multiplicity As hcard hinter
  have hcs : (∑ a ∈ Finset.univ.biUnion As,
        ((Finset.univ.filter fun i ↦ a ∈ As i).card : ℤ)) ^ 2
      ≤ (∑ a ∈ Finset.univ.biUnion As, ((Finset.univ.filter fun i ↦ a ∈ As i).card : ℤ) ^ 2) *
        (Finset.univ.biUnion As).card := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ.biUnion As)
      (fun a ↦ ((Finset.univ.filter fun i ↦ a ∈ As i).card : ℤ)) (fun _ ↦ (1 : ℤ))
    simp only [mul_one, one_pow, Finset.sum_const, nsmul_eq_mul] at h
    exact h
  rw [c1, c2] at hcs
  -- Since `495² = 1485 * 165`, we conclude that the union has at least 165 elements.
  have key : (165 : ℤ) ≤ (Finset.univ.biUnion As).card := by
    have e : (495 : ℤ) ^ 2 = 1485 * 165 := by norm_num
    rw [e] at hcs
    exact (mul_le_mul_iff_right₀ (by norm_num : (0 : ℤ) < 1485)).mp hcs
  exact_mod_cast key

problem usa2011_p6_sharp :
    ∃ A : Finset (Finset (Fin 11) ⊕ Fin 60),
      ∃ As : Fin 11 → Finset (Finset (Fin 11) ⊕ Fin 60),
        A.card = 225 ∧ (∀ i, As i ⊆ A) ∧ (∀ i, (As i).card = 45) ∧
        (∀ i j, i ≠ j → (As i ∩ As j).card = 9) ∧
        (Finset.univ.biUnion As).card = 165 := by
  -- The example: the ground set consists of the `Nat.choose 11 3 = 165` three-element
  -- subsets of `Fin 11` together with 60 extra elements; `As i` consists of the
  -- three-element subsets containing `i`.
  set U₀ : Finset (Finset (Fin 11)) := Finset.univ.powersetCard 3 with hU₀
  set A : Finset (Finset (Fin 11) ⊕ Fin 60) :=
    U₀.image Sum.inl ∪ Finset.univ.image Sum.inr with hA
  set As : Fin 11 → Finset (Finset (Fin 11) ⊕ Fin 60) :=
    fun i ↦ (U₀.filter fun T ↦ i ∈ T).image Sum.inl with hAs
  refine ⟨A, As, ?_, ?_, ?_, ?_, ?_⟩
  · -- `|A| = 165 + 60 = 225`.
    have hdisj : Disjoint (U₀.image Sum.inl : Finset (Finset (Fin 11) ⊕ Fin 60))
        (Finset.univ.image Sum.inr) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      rcases Finset.mem_image.mp hx1 with ⟨T, _, rfl⟩
      rcases Finset.mem_image.mp hx2 with ⟨y, _, h⟩
      simp at h
    rw [hA, Finset.card_union_of_disjoint hdisj,
      Finset.card_image_of_injective _ Sum.inl_injective,
      Finset.card_image_of_injective _ Sum.inr_injective, Finset.card_powersetCard,
      Finset.card_univ, Fintype.card_fin, Finset.card_univ, Fintype.card_fin]
    decide
  · -- Each `As i` is contained in `A`.
    intro i x hx
    simp only [hAs] at hx
    rcases Finset.mem_image.mp hx with ⟨T, hT, rfl⟩
    rw [hA]
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨T, (Finset.mem_filter.mp hT).1, rfl⟩)
  · -- `|As i| = 45`.
    intro i
    simp only [hAs]
    rw [Finset.card_image_of_injective _ Sum.inl_injective, hU₀]
    exact card_powersetCard_filter_mem i
  · -- `|As i ∩ As j| = 9` for `i ≠ j`.
    intro i j hij
    have hfi : (U₀.filter fun T ↦ i ∈ T) ∩ (U₀.filter fun T ↦ j ∈ T)
        = U₀.filter fun T ↦ i ∈ T ∧ j ∈ T := by
      ext T
      simp only [Finset.mem_inter, Finset.mem_filter]
      tauto
    have hinter : ((U₀.filter fun T ↦ i ∈ T).image Sum.inl ∩
        (U₀.filter fun T ↦ j ∈ T).image Sum.inl : Finset (Finset (Fin 11) ⊕ Fin 60))
        = (U₀.filter fun T ↦ i ∈ T ∧ j ∈ T).image Sum.inl := by
      rw [← hfi, Finset.image_inter _ _ Sum.inl_injective]
    simp only [hAs]
    rw [hinter, Finset.card_image_of_injective _ Sum.inl_injective, hU₀]
    exact card_powersetCard_filter_mem₂ hij
  · -- The union of the `As i` is the set of all three-element subsets, of size 165.
    have hunion : (Finset.univ.biUnion fun i ↦ (U₀.filter fun T ↦ i ∈ T).image Sum.inl :
        Finset (Finset (Fin 11) ⊕ Fin 60)) = U₀.image Sum.inl := by
      ext x
      constructor
      · intro hx
        rw [Finset.mem_biUnion] at hx
        obtain ⟨i, _, hx⟩ := hx
        rcases Finset.mem_image.mp hx with ⟨T, hT, rfl⟩
        exact Finset.mem_image.mpr ⟨T, (Finset.mem_filter.mp hT).1, rfl⟩
      · intro hx
        rcases Finset.mem_image.mp hx with ⟨T, hT, rfl⟩
        rw [hU₀, Finset.mem_powersetCard] at hT
        obtain ⟨hTsub, hTcard⟩ := hT
        have hne : T.Nonempty := by rw [← Finset.card_pos, hTcard]; decide
        obtain ⟨i, hi⟩ := hne
        rw [Finset.mem_biUnion]
        exact ⟨i, Finset.mem_univ i, Finset.mem_image.mpr ⟨T,
          Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨hTsub, hTcard⟩, hi⟩, rfl⟩⟩
    simp only [hAs]
    rw [hunion, Finset.card_image_of_injective _ Sum.inl_injective, hU₀,
      Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
    decide

end Usa2011P6
