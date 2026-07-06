/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Olympiad 1988, Problem 2

Let n be a positive integer and let A₁, A₂, ..., A₂ₙ₊₁ be subsets
of a set B. Suppose that

(i) each Aᵢ has exactly 2n elements,
(ii) each intersection Aᵢ ∩ Aⱼ (i ≠ j) contains exactly one element, and
(iii) every element of B belongs to at least two of the Aᵢ.

For which values of n can one assign to every element of B
one of the numbers 0 and 1 in such a way that each Aᵢ has
exactly n elements assigned 0?
-/

namespace Imo1988P2

determine SolutionSet : Set ℕ := {n | 0 < n ∧ Even n}

snip begin

/-- Counting the pairs `(a, b)` with `a ∈ s`, `b ∈ t` and `r a b`,
fiberwise in either order. -/
lemma double_count {α β : Type*} (s : Finset α) (t : Finset β) (r : α → β → Prop)
    [∀ a b, Decidable (r a b)] :
    ∑ a ∈ s, (t.filter (fun b ↦ r a b)).card =
      ∑ b ∈ t, (s.filter (fun a ↦ r a b)).card := by
  simp only [Finset.card_filter]
  exact Finset.sum_comm

/-- If finitely many terms, each at least `1`, sum to the number of terms,
then every term equals `1`. -/
lemma all_eq_one {α : Type*} {s : Finset α} {g : α → ℕ}
    (h1 : ∀ a ∈ s, 1 ≤ g a) (h2 : ∑ a ∈ s, g a = s.card) :
    ∀ a ∈ s, g a = 1 := by
  intro a ha
  have h3 : ∑ a ∈ s, 1 = ∑ a ∈ s, g a := by
    rw [h2, Finset.sum_const_nat fun x _ ↦ rfl, mul_one]
  exact ((Finset.sum_eq_sum_iff_of_le h1).mp h3 a ha).symm

section Structure

variable {n : ℕ} {B : Type} [DecidableEq B] {A : Fin (2 * n + 1) → Finset B}

/-- Under the problem's hypotheses, every element of `A i` lies in exactly one
set `A j` with `j ≠ i`. -/
lemma other_unique
    (hcard : ∀ i, (A i).card = 2 * n)
    (hint : ∀ i j, i ≠ j → (A i ∩ A j).card = 1)
    (hcov : ∀ b : B, 2 ≤ (Finset.univ.filter (fun i ↦ b ∈ A i)).card)
    {i : Fin (2 * n + 1)} {b : B} (hb : b ∈ A i) :
    ((Finset.univ.erase i).filter (fun j ↦ b ∈ A j)).card = 1 := by
  have key : ∀ a ∈ A i, ((Finset.univ.erase i).filter (fun j ↦ a ∈ A j)).card = 1 := by
    refine all_eq_one (fun a ha ↦ ?_) ?_
    · have h2 := hcov a
      have h3 : (Finset.univ.filter (fun j ↦ a ∈ A j)).card - 1 ≤
          ((Finset.univ.erase i).filter (fun j ↦ a ∈ A j)).card := by
        rw [Finset.filter_erase]
        exact Finset.pred_card_le_card_erase
      lia
    · rw [double_count (A i) (Finset.univ.erase i) (fun a j ↦ a ∈ A j)]
      have hterm : ∀ j ∈ Finset.univ.erase i,
          ((A i).filter (fun a ↦ a ∈ A j)).card = 1 := by
        intro j hj
        rw [Finset.filter_mem_eq_inter]
        exact hint i j (Finset.mem_erase.mp hj).1.symm
      rw [Finset.sum_const_nat hterm, mul_one,
        Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
        Fintype.card_fin, hcard i]
      lia
  exact key b hb

/-- The pair of indices of the sets containing a common element `b` of
`A i` and `A j`. -/
lemma pair_eq
    (hcard : ∀ i, (A i).card = 2 * n)
    (hint : ∀ i j, i ≠ j → (A i ∩ A j).card = 1)
    (hcov : ∀ b : B, 2 ≤ (Finset.univ.filter (fun i ↦ b ∈ A i)).card)
    {i j : Fin (2 * n + 1)} {b : B} (hbi : b ∈ A i) (hbj : b ∈ A j) (hij : i ≠ j) :
    Finset.univ.filter (fun k ↦ b ∈ A k) = {i, j} := by
  have h1 : ((Finset.univ.filter (fun k ↦ b ∈ A k)).erase i).card = 1 := by
    rw [← Finset.filter_erase]
    exact other_unique hcard hint hcov hbi
  have h2 : i ∈ Finset.univ.filter (fun k ↦ b ∈ A k) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbi⟩
  have h3 := Finset.card_erase_of_mem h2
  have h4 : 0 < (Finset.univ.filter (fun k ↦ b ∈ A k)).card :=
    Finset.card_pos.mpr ⟨i, h2⟩
  have hsub : ({i, j} : Finset (Fin (2 * n + 1))) ⊆
      Finset.univ.filter (fun k ↦ b ∈ A k) := by
    intro k hk
    rw [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl
    · exact h2
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbj⟩
  have h5 : ({i, j} : Finset (Fin (2 * n + 1))).card = 2 :=
    Finset.card_pair_eq_two_iff.mpr hij
  exact (Finset.eq_of_subset_of_card_le hsub (by lia)).symm

end Structure

/-- Colour an edge `e = {p, q}` of the complete graph on `Fin (K + 1)` with `0`
iff the difference of its endpoints, in one of the two directions,
lies in `[1, m]`. -/
def colour {K : ℕ} (m : ℕ) (e : Finset (Fin (K + 1))) : Fin 2 :=
  if ∃ p ∈ e, ∃ q ∈ e, (q - p).val ∈ Finset.Icc 1 m then 0 else 1

lemma colour_eq_zero_iff {K m : ℕ} {e : Finset (Fin (K + 1))} :
    colour m e = 0 ↔ ∃ p ∈ e, ∃ q ∈ e, (q - p).val ∈ Finset.Icc 1 m := by
  unfold colour
  split
  · next h => exact iff_of_true rfl h
  · next h => exact iff_of_false (by decide) h

lemma colour_pair_eq_zero_iff {K m : ℕ} {i j : Fin (K + 1)} :
    colour m {i, j} = 0 ↔
      ((j - i).val ∈ Finset.Icc 1 m ∨ (i - j).val ∈ Finset.Icc 1 m) := by
  rw [colour_eq_zero_iff]
  have hz : ∀ x : Fin (K + 1), (x - x).val ∉ Finset.Icc 1 m := by
    intro x
    rw [sub_self]
    simp
  constructor
  · rintro ⟨p, hp, q, hq, h⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq
    rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
    · exact absurd h (hz _)
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h (hz _)
  · rintro (h | h)
    · exact ⟨i, Finset.mem_insert_self i _,
        j, Finset.mem_insert_of_mem (Finset.mem_singleton_self j), h⟩
    · exact ⟨j, Finset.mem_insert_of_mem (Finset.mem_singleton_self j),
        i, Finset.mem_insert_self i _, h⟩

/-- At each vertex `i` of the complete graph on `Fin (2 * n + 1)` with
`n = 2 * m`, exactly `n` of the `2 * n` incident edges have a circular
difference in `[1, m]`: measuring each neighbour `j` by `(j - i).val`
identifies the good neighbours with `[1, m] ∪ [2 * n + 1 - m, 2 * n]`. -/
lemma count_good {n m : ℕ} (hm : n = 2 * m) (i : Fin (2 * n + 1)) :
    ((Finset.univ.erase i).filter
      (fun j ↦ (j - i).val ∈ Finset.Icc 1 m ∨ (i - j).val ∈ Finset.Icc 1 m)).card
      = n := by
  have key : ((Finset.univ.erase i).filter
      (fun j ↦ (j - i).val ∈ Finset.Icc 1 m ∨ (i - j).val ∈ Finset.Icc 1 m)).card =
      ((Finset.range (2 * n + 1)).filter
      (fun x ↦ 1 ≤ x ∧ (x ≤ m ∨ 2 * n + 1 - m ≤ x))).card := by
    refine Finset.card_bij (fun j _ ↦ (j - i).val) ?_ ?_ ?_
    · intro j hj
      rw [Finset.mem_filter, Finset.mem_erase] at hj
      obtain ⟨⟨hji, -⟩, hgood⟩ := hj
      have hne : j - i ≠ 0 := sub_ne_zero_of_ne hji
      have hne' : (j - i).val ≠ 0 :=
        fun h ↦ hne (Fin.val_inj.mp (by rw [h, Fin.val_zero]))
      have hvn := Fin.val_neg (j - i)
      rw [if_neg hne, neg_sub] at hvn
      have hlt := (j - i).isLt
      simp only [Finset.mem_Icc] at hgood
      rw [hvn] at hgood
      rw [Finset.mem_filter, Finset.mem_range]
      refine ⟨hlt, by lia, ?_⟩
      rcases hgood with h | h
      · exact Or.inl h.2
      · exact Or.inr (by lia)
    · intro j₁ _ j₂ _ h
      have h' := congrArg (· + i) (Fin.val_inj.mp h)
      simpa [sub_add_cancel] using h'
    · intro x hx
      rw [Finset.mem_filter, Finset.mem_range] at hx
      obtain ⟨hlt, hx1, hxor⟩ := hx
      have hxv : (⟨x, hlt⟩ : Fin (2 * n + 1)) + i - i = ⟨x, hlt⟩ :=
        add_sub_cancel_right _ i
      refine ⟨⟨x, hlt⟩ + i, ?_, by rw [hxv]⟩
      have hc0 : (⟨x, hlt⟩ : Fin (2 * n + 1)) ≠ 0 := by
        intro h
        rw [Fin.ext_iff, Fin.val_zero] at h
        have hx0 : x = 0 := h
        lia
      rw [Finset.mem_filter, Finset.mem_erase]
      refine ⟨⟨fun heq ↦ hc0 (by rw [← hxv, heq, sub_self]), Finset.mem_univ _⟩, ?_⟩
      have hvn := Fin.val_neg (⟨x, hlt⟩ : Fin (2 * n + 1))
      rw [if_neg hc0] at hvn
      have hisub : i - ((⟨x, hlt⟩ : Fin (2 * n + 1)) + i) = -⟨x, hlt⟩ := by
        rw [← neg_sub (⟨x, hlt⟩ + i) i, hxv]
      have hval : (⟨x, hlt⟩ : Fin (2 * n + 1)).val = x := rfl
      rw [hxv, hisub, hvn, hval]
      simp only [Finset.mem_Icc]
      rcases hxor with h | h
      · exact Or.inl ⟨hx1, h⟩
      · refine Or.inr ⟨?_, ?_⟩ <;> lia
  have he : (Finset.range (2 * n + 1)).filter
      (fun x ↦ 1 ≤ x ∧ (x ≤ m ∨ 2 * n + 1 - m ≤ x)) =
      Finset.Icc 1 m ∪ Finset.Icc (n + m + 1) (2 * n) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union, Finset.mem_Icc]
    lia
  have hd : Disjoint (Finset.Icc 1 m) (Finset.Icc (n + m + 1) (2 * n)) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    rw [Finset.mem_Icc] at hx hx'
    lia
  rw [key, he, Finset.card_union_eq_card_add_card.mpr hd, Nat.card_Icc, Nat.card_Icc]
  lia

section VertexCount

variable {n : ℕ} {B : Type} [DecidableEq B] {A : Fin (2 * n + 1) → Finset B}

/-- With `n = 2 * m`, colouring each element by `colour m` of its index pair
gives exactly `n` elements of colour `0` in each `A i`. -/
lemma vertex_count {m : ℕ} (hm : n = 2 * m)
    (hcard : ∀ i, (A i).card = 2 * n)
    (hint : ∀ i j, i ≠ j → (A i ∩ A j).card = 1)
    (hcov : ∀ b : B, 2 ≤ (Finset.univ.filter (fun i ↦ b ∈ A i)).card)
    (i : Fin (2 * n + 1)) :
    ((A i).filter
      (fun b ↦ colour m (Finset.univ.filter (fun k ↦ b ∈ A k)) = 0)).card = n := by
  have key := double_count
    ((A i).filter (fun b ↦ colour m (Finset.univ.filter (fun k ↦ b ∈ A k)) = 0))
    (Finset.univ.erase i) (fun b j ↦ b ∈ A j)
  have hL : ∀ b ∈ (A i).filter
      (fun b ↦ colour m (Finset.univ.filter (fun k ↦ b ∈ A k)) = 0),
      ((Finset.univ.erase i).filter (fun j ↦ b ∈ A j)).card = 1 :=
    fun b hb ↦ other_unique hcard hint hcov (Finset.mem_filter.mp hb).1
  rw [Finset.sum_const_nat hL, mul_one] at key
  have hR : ∀ j ∈ Finset.univ.erase i,
      (((A i).filter
        (fun b ↦ colour m (Finset.univ.filter (fun k ↦ b ∈ A k)) = 0)).filter
        (fun b ↦ b ∈ A j)).card =
      if (j - i).val ∈ Finset.Icc 1 m ∨ (i - j).val ∈ Finset.Icc 1 m
      then 1 else 0 := by
    intro j hj
    have hij : i ≠ j := (Finset.mem_erase.mp hj).1.symm
    obtain ⟨b₀, hb₀⟩ := Finset.card_eq_one.mp (hint i j hij)
    have hb₀m : b₀ ∈ A i ∩ A j := by
      rw [hb₀]
      exact Finset.mem_singleton_self b₀
    have hb₀i : b₀ ∈ A i := (Finset.mem_inter.mp hb₀m).1
    have hb₀j : b₀ ∈ A j := (Finset.mem_inter.mp hb₀m).2
    have hpair : Finset.univ.filter (fun k ↦ b₀ ∈ A k) = {i, j} :=
      pair_eq hcard hint hcov hb₀i hb₀j hij
    have hcol : (colour m (Finset.univ.filter (fun k ↦ b₀ ∈ A k)) = 0) ↔
        ((j - i).val ∈ Finset.Icc 1 m ∨ (i - j).val ∈ Finset.Icc 1 m) := by
      rw [hpair]
      exact colour_pair_eq_zero_iff
    rw [Finset.filter_comm, Finset.filter_mem_eq_inter, hb₀, Finset.filter_singleton,
      apply_ite Finset.card, Finset.card_singleton, Finset.card_empty]
    simp only [hcol]
  rw [Finset.sum_congr rfl hR, ← Finset.card_filter] at key
  rw [key]
  exact count_good hm i

end VertexCount

/-- The edges of the complete graph on `Fin N`: two-element subsets. -/
abbrev Edges (N : ℕ) : Type := {e : Finset (Fin N) // e.card = 2}

/-- The set of edges incident to the vertex `i`. -/
def edgeSets (N : ℕ) (i : Fin N) : Finset (Edges N) :=
  Finset.univ.filter (fun e ↦ i ∈ e.val)

lemma mem_edgeSets {N : ℕ} {i : Fin N} {e : Edges N} :
    e ∈ edgeSets N i ↔ i ∈ e.val := by
  rw [edgeSets, Finset.mem_filter]
  exact and_iff_right (Finset.mem_univ e)

lemma edgeSets_card {N : ℕ} (i : Fin N) : (edgeSets N i).card = N - 1 := by
  have h : (Finset.univ.erase i).card = (edgeSets N i).card := by
    refine Finset.card_bij
      (fun j hj ↦ ⟨{i, j}, Finset.card_pair_eq_two_iff.mpr
        (Finset.mem_erase.mp hj).1.symm⟩) ?_ ?_ ?_
    · intro j hj
      exact mem_edgeSets.mpr (Finset.mem_insert_self i _)
    · intro j₁ h₁ j₂ h₂ heq
      have hv : ({i, j₁} : Finset (Fin N)) = {i, j₂} := congrArg Subtype.val heq
      have hmem : j₁ ∈ ({i, j₂} : Finset (Fin N)) := by
        rw [← hv]
        exact Finset.mem_insert_of_mem (Finset.mem_singleton_self j₁)
      rcases Finset.mem_insert.mp hmem with h | h
      · exact absurd h (Finset.mem_erase.mp h₁).1
      · exact Finset.mem_singleton.mp h
    · intro e he
      obtain ⟨x, y, hxy, hval⟩ := Finset.card_eq_two.mp e.prop
      have hi : i ∈ e.val := mem_edgeSets.mp he
      rw [hval, Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl
      · exact ⟨y, Finset.mem_erase.mpr ⟨hxy.symm, Finset.mem_univ y⟩,
          Subtype.ext hval.symm⟩
      · refine ⟨x, Finset.mem_erase.mpr ⟨hxy, Finset.mem_univ x⟩, Subtype.ext ?_⟩
        rw [hval]
        exact Finset.pair_comm i x
  rw [← h, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
    Fintype.card_fin]

lemma edgeSets_inter {N : ℕ} {i j : Fin N} (hij : i ≠ j) :
    edgeSets N i ∩ edgeSets N j =
      {⟨{i, j}, Finset.card_pair_eq_two_iff.mpr hij⟩} := by
  ext e
  rw [Finset.mem_inter, Finset.mem_singleton, mem_edgeSets, mem_edgeSets]
  constructor
  · rintro ⟨hi, hj⟩
    have hsub : ({i, j} : Finset (Fin N)) ⊆ e.val :=
      Finset.insert_subset hi (Finset.singleton_subset_iff.mpr hj)
    have hcards : e.val.card ≤ ({i, j} : Finset (Fin N)).card := by
      rw [e.prop]
      exact le_of_eq (Finset.card_pair_eq_two_iff.mpr hij).symm
    exact Subtype.ext (Finset.eq_of_subset_of_card_le hsub hcards).symm
  · rintro rfl
    exact ⟨Finset.mem_insert_self i _,
      Finset.mem_insert_of_mem (Finset.mem_singleton_self j)⟩

lemma edgeSets_cov {N : ℕ} (e : Edges N) :
    (Finset.univ.filter (fun i ↦ e ∈ edgeSets N i)).card = 2 := by
  have h : Finset.univ.filter (fun i ↦ e ∈ edgeSets N i) = e.val := by
    ext i
    rw [Finset.mem_filter, mem_edgeSets]
    exact and_iff_right (Finset.mem_univ i)
  rw [h, e.prop]

snip end

problem imo1988_p2 (n : ℕ) :
    n ∈ SolutionSet ↔
    (0 < n ∧
     ∀ (B : Type) [DecidableEq B] (A : Fin (2 * n + 1) → Finset B),
       (∀ i, (A i).card = 2 * n) →
       (∀ i j, i ≠ j → (A i ∩ A j).card = 1) →
       (∀ b : B, 2 ≤ (Finset.univ.filter (fun i ↦ b ∈ A i)).card) →
       ∃ f : B → Fin 2, ∀ i, ((A i).filter (fun b ↦ f b = 0)).card = n) := by
  constructor
  · rintro ⟨hn, m, hm⟩
    refine ⟨hn, ?_⟩
    intro B _inst A hcard hint hcov
    have hm' : n = 2 * m := by lia
    exact ⟨fun b ↦ colour m (Finset.univ.filter (fun k ↦ b ∈ A k)),
           fun i ↦ vertex_count hm' hcard hint hcov i⟩
  · rintro ⟨hn, H⟩
    obtain ⟨f, hf⟩ := H (Edges (2 * n + 1)) (edgeSets (2 * n + 1))
      (fun i ↦ by rw [edgeSets_card]; lia)
      (fun i j hij ↦ by rw [edgeSets_inter hij, Finset.card_singleton])
      (fun e ↦ le_of_eq (edgeSets_cov e).symm)
    refine ⟨hn, ?_⟩
    have key := double_count (Finset.univ.filter (fun e ↦ f e = 0))
      (Finset.univ : Finset (Fin (2 * n + 1))) (fun e i ↦ e ∈ edgeSets (2 * n + 1) i)
    have hL : ∀ e ∈ Finset.univ.filter (fun e ↦ f e = 0),
        (Finset.univ.filter (fun i ↦ e ∈ edgeSets (2 * n + 1) i)).card = 2 :=
      fun e _ ↦ edgeSets_cov e
    rw [Finset.sum_const_nat hL] at key
    have hR : ∀ i ∈ (Finset.univ : Finset (Fin (2 * n + 1))),
        ((Finset.univ.filter (fun e ↦ f e = 0)).filter
          (fun e ↦ e ∈ edgeSets (2 * n + 1) i)).card = n := by
      intro i _
      have h : (Finset.univ.filter (fun e ↦ f e = 0)).filter
          (fun e ↦ e ∈ edgeSets (2 * n + 1) i) =
          (edgeSets (2 * n + 1) i).filter (fun e ↦ f e = 0) := by
        rw [Finset.filter_comm, Finset.filter_mem_eq_inter, Finset.univ_inter]
      rw [h]
      exact hf i
    rw [Finset.sum_const_nat hR, Finset.card_univ, Fintype.card_fin] at key
    have heven : Even ((2 * n + 1) * n) :=
      ⟨(Finset.univ.filter (fun e ↦ f e = 0)).card, by lia⟩
    exact (Nat.even_mul.mp heven).resolve_left
      fun h ↦ Nat.even_add_one.mp h (even_two_mul n)

end Imo1988P2
