/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics] }

/-!
# USA Mathematical Olympiad 1978, Problem 5

There are 9 delegates at a conference, each speaking at most three languages.
Given any three delegates, at least 2 speak a common language.
Show that there are three delegates with a common language.
-/

namespace Usa1978P5

/-- Delegate `a` and delegate `b` speak a common language. -/
abbrev Share {L : Type*} (speaks : Fin 9 → Finset L) (a b : Fin 9) : Prop :=
  ∃ l : L, l ∈ speaks a ∧ l ∈ speaks b

snip begin

open Classical

/-- The delegates other than `d` that share a language with `d`. -/
noncomputable abbrev SharedWith {L : Type*} (speaks : Fin 9 → Finset L) (d : Fin 9) :
    Finset (Fin 9) :=
  Finset.univ.filter fun b => b ≠ d ∧ Share speaks d b

/-- Assuming that no three delegates share a common language, a delegate `d` can
share a language with at most three other delegates: among any four delegates
sharing a language with `d`, two of them would share the *same* language with `d`
by the pigeonhole principle, since `d` speaks at most three languages, and those
two together with `d` would be three delegates with a common language. -/
theorem card_sharedWith_le {L : Type*} (speaks : Fin 9 → Finset L)
    (hthree : ∀ d : Fin 9, (speaks d).card ≤ 3)
    (hnothree : ¬∃ a b c : Fin 9, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      ∃ l : L, l ∈ speaks a ∧ l ∈ speaks b ∧ l ∈ speaks c)
    (d : Fin 9) : (SharedWith speaks d).card ≤ 3 := by
  by_contra h
  push Not at h
  have hsh : ∀ b : {x // x ∈ SharedWith speaks d}, ∃ l : L, l ∈ speaks d ∧ l ∈ speaks b.1 :=
    fun b => (Finset.mem_filter.mp b.2).2.2
  choose f hf using hsh
  obtain ⟨x, -, y, -, hxy, hfxy⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to
      (s := (SharedWith speaks d).attach) (t := speaks d) (f := f)
      (by rw [Finset.card_attach]; exact lt_of_le_of_lt (hthree d) h)
      (fun b _ => (hf b).1)
  have hdx : d ≠ x.1 := ((Finset.mem_filter.mp x.2).2.1).symm
  have hdy : d ≠ y.1 := ((Finset.mem_filter.mp y.2).2.1).symm
  have hxy1 : x.1 ≠ y.1 := fun h => hxy (Subtype.ext h)
  have hfy : f x ∈ speaks y.1 := by rw [hfxy]; exact (hf y).2
  exact hnothree ⟨d, x.1, y.1, hdx, hdy, hxy1, f x, (hf x).1, (hf x).2, hfy⟩

snip end

problem usa1978_p5 {L : Type*} (speaks : Fin 9 → Finset L)
    (hthree : ∀ d : Fin 9, (speaks d).card ≤ 3)
    (hpair : ∀ a b c : Fin 9, a ≠ b → a ≠ c → b ≠ c →
      Share speaks a b ∨ Share speaks b c ∨ Share speaks a c) :
    ∃ a b c : Fin 9, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      ∃ l : L, l ∈ speaks a ∧ l ∈ speaks b ∧ l ∈ speaks c := by
  by_contra hnothree
  have h1 : ∀ d : Fin 9, (SharedWith speaks d).card ≤ 3 :=
    card_sharedWith_le speaks hthree hnothree
  -- Fix a delegate `A`. At most four delegates are `A` itself or share a language
  -- with `A`, so some delegate `B` is neither.
  obtain ⟨A⟩ : Nonempty (Fin 9) := ⟨0⟩
  have hcardA : (SharedWith speaks A ∪ {A}).card ≤ 4 := by
    have h2 := Finset.card_union_le (SharedWith speaks A) {A}
    have hA3 := h1 A
    simp only [Finset.card_singleton] at h2
    omega
  obtain ⟨B, hB⟩ : ∃ B : Fin 9, B ∉ SharedWith speaks A ∪ {A} := by
    by_contra hB
    push Not at hB
    have hle := Finset.card_le_card (s := (Finset.univ : Finset (Fin 9)))
      (t := SharedWith speaks A ∪ {A}) (fun x _ => hB x)
    simp only [Finset.card_univ, Fintype.card_fin] at hle
    omega
  have hBA : B ≠ A :=
    fun h => hB (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have hnAB : ¬Share speaks A B :=
    fun h => hB (Finset.mem_union_left _
      (Finset.mem_filter.mpr ⟨Finset.mem_univ B, hBA, h⟩))
  -- At most eight delegates are `A`, are `B`, or share a language with one of
  -- them, so some delegate `C` shares a language with neither `A` nor `B`.
  have hcardC : (SharedWith speaks A ∪ SharedWith speaks B ∪ {A, B}).card ≤ 8 := by
    have h2 := Finset.card_union_le (SharedWith speaks A ∪ SharedWith speaks B) {A, B}
    have h3 := Finset.card_union_le (SharedWith speaks A) (SharedWith speaks B)
    have hA3 := h1 A
    have hB3 := h1 B
    have h4 : ({A, B} : Finset (Fin 9)).card ≤ 2 :=
      calc ({A, B} : Finset (Fin 9)).card
          ≤ ({B} : Finset (Fin 9)).card + 1 := Finset.card_insert_le _ _
        _ = 2 := by simp
    omega
  obtain ⟨C, hC⟩ :
      ∃ C : Fin 9, C ∉ SharedWith speaks A ∪ SharedWith speaks B ∪ {A, B} := by
    by_contra hC
    push Not at hC
    have hle := Finset.card_le_card (s := (Finset.univ : Finset (Fin 9)))
      (t := SharedWith speaks A ∪ SharedWith speaks B ∪ {A, B}) (fun x _ => hC x)
    simp only [Finset.card_univ, Fintype.card_fin] at hle
    omega
  have hCA : C ≠ A :=
    fun h => hC (Finset.mem_union_right _ (Finset.mem_insert.mpr (Or.inl h)))
  have hCB : C ≠ B :=
    fun h => hC (Finset.mem_union_right _
      (Finset.mem_insert_of_mem (Finset.mem_singleton.mpr h)))
  have hnAC : ¬Share speaks A C :=
    fun h => hC (Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_filter.mpr ⟨Finset.mem_univ C, hCA, h⟩)))
  have hnBC : ¬Share speaks B C :=
    fun h => hC (Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_filter.mpr ⟨Finset.mem_univ C, hCB, h⟩)))
  -- No two of `A`, `B`, `C` share a language, contradicting the hypothesis.
  rcases hpair A B C hBA.symm hCA.symm hCB.symm with h | h | h
  · exact hnAB h
  · exact hnBC h
  · exact hnAC h

end Usa1978P5
