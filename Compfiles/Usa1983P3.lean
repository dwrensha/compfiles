/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Tactic.Choose
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics] }

/-!
# USA Mathematical Olympiad 1983, Problem 3

S₁, S₂, ..., Sₙ are subsets of the real line. Each Sᵢ is the union of two
closed intervals. Any three Sᵢ have a point in common. Show that there is a
point which belongs to at least half the Sᵢ.
-/

namespace Usa1983P3

snip begin

/-- Key covering step of the solution: writing each set of the family as
`Icc (a i) (b i) ∪ Icc (c i) (d i)`, every set contains either `a h`, where `h`
maximizes the left endpoint `a`, or `d k`, where `k` minimizes the right
endpoint `d`. Otherwise a common point of `S i`, `S h` and `S k` would have to
lie left of `a h` inside `S h`, or right of `d k` inside `S k`. -/
lemma mem_leftMax_or_rightMin {n : ℕ} {S : Fin n → Set ℝ}
    {a b c d : Fin n → ℝ} (hab : ∀ i, a i ≤ b i) (hbc : ∀ i, b i ≤ c i)
    (hcd : ∀ i, c i ≤ d i)
    (hSd : ∀ i, S i = Set.Icc (a i) (b i) ∪ Set.Icc (c i) (d i))
    {h k : Fin n} (hmax : ∀ i, a i ≤ a h) (hmin : ∀ i, d k ≤ d i)
    (h3 : ∀ i j k : Fin n, (S i ∩ S j ∩ S k).Nonempty) (i : Fin n) :
    a h ∈ S i ∨ d k ∈ S i := by
  by_contra hcon
  push Not at hcon
  obtain ⟨haS, hdS⟩ := hcon
  -- Since `a i ≤ a h` and `a h ∉ S i`, the point `a h` lies right of `b i`.
  have hbi : b i < a h := by
    have h1 : a h ∉ Set.Icc (a i) (b i) := by
      intro hm
      apply haS
      rw [hSd i]
      exact Set.mem_union_left _ hm
    rw [Set.mem_Icc, not_and] at h1
    exact lt_of_not_ge (h1 (hmax i))
  -- Since `d k ≤ d i` and `d k ∉ S i`, the point `d k` lies left of `c i`.
  have hck : d k < c i := by
    have h1 : d k ∉ Set.Icc (c i) (d i) := by
      intro hm
      apply hdS
      rw [hSd i]
      exact Set.mem_union_right _ hm
    rw [Set.mem_Icc, not_and'] at h1
    exact lt_of_not_ge (h1 (hmin i))
  obtain ⟨x, ⟨⟨hxi, hxh⟩, hxk⟩⟩ := h3 i h k
  -- Any point of `S h` is at least `a h`.
  have hah : a h ≤ x := by
    rw [hSd h] at hxh
    rcases hxh with hx | hx
    · exact (Set.mem_Icc.mp hx).1
    · exact ((hab h).trans (hbc h)).trans (Set.mem_Icc.mp hx).1
  -- Any point of `S k` is at most `d k`.
  have hxd : x ≤ d k := by
    rw [hSd k] at hxk
    rcases hxk with hx | hx
    · exact ((Set.mem_Icc.mp hx).2.trans (hbc k)).trans (hcd k)
    · exact (Set.mem_Icc.mp hx).2
  rw [hSd i] at hxi
  rcases hxi with hx | hx
  · exact absurd ((Set.mem_Icc.mp hx).2.trans_lt hbi) (not_lt_of_ge hah)
  · exact absurd (hck.trans_le (Set.mem_Icc.mp hx).1) (not_lt_of_ge hxd)

snip end

problem usa1983_p3 {n : ℕ} (hn : 0 < n) (S : Fin n → Set ℝ)
    (hS : ∀ i, ∃ a b c d : ℝ, a ≤ b ∧ b ≤ c ∧ c ≤ d ∧
      S i = Set.Icc a b ∪ Set.Icc c d)
    (h3 : ∀ i j k : Fin n, (S i ∩ S j ∩ S k).Nonempty) :
    ∃ x : ℝ, n ≤ 2 * {i : Fin n | x ∈ S i}.ncard := by
  choose a b c d hab hbc hcd hSd using hS
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨h, -, hmax⟩ := Finset.exists_max_image Finset.univ a Finset.univ_nonempty
  obtain ⟨k, -, hmin⟩ := Finset.exists_min_image Finset.univ d Finset.univ_nonempty
  have hmax' : ∀ i, a i ≤ a h := fun i ↦ hmax i (Finset.mem_univ i)
  have hmin' : ∀ i, d k ≤ d i := fun i ↦ hmin i (Finset.mem_univ i)
  have hcover : ∀ i : Fin n, a h ∈ S i ∨ d k ∈ S i :=
    fun i ↦ mem_leftMax_or_rightMin hab hbc hcd hSd hmax' hmin' h3 i
  -- Every index contains `a h` or `d k`, so one of them is in at least half.
  have hsub : (Set.univ : Set (Fin n)) ⊆
      {i : Fin n | a h ∈ S i} ∪ {i : Fin n | d k ∈ S i} :=
    fun i _ ↦ hcover i
  have hcard : n ≤ {i : Fin n | a h ∈ S i}.ncard +
      {i : Fin n | d k ∈ S i}.ncard := by
    have h1 : (Set.univ : Set (Fin n)).ncard ≤
        ({i : Fin n | a h ∈ S i} ∪ {i : Fin n | d k ∈ S i}).ncard :=
      Set.ncard_le_ncard hsub
    rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at h1
    exact h1.trans (Set.ncard_union_le _ _)
  rcases le_or_gt {i : Fin n | d k ∈ S i}.ncard {i : Fin n | a h ∈ S i}.ncard
    with hle | hgt
  · exact ⟨a h, by lia⟩
  · exact ⟨d k, by lia⟩

end Usa1983P3
