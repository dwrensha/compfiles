/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# USA Mathematical Olympiad 2002, Problem 1

Let S be a set with 2002 elements, and let N be an integer with

  0 ≤ N ≤ 2^2002.

Prove that it is possible to color every subset of S either blue or
red so that the following conditions hold:

 a) the union of any two red subsets is red;
 b) the union of any two blue subsets is blue;
 c) there are exactly N red subsets.
-/

namespace Usa2002P1

inductive Color : Type where
| red : Color
| blue : Color
deriving DecidableEq, Fintype

snip begin

-- Seems like this maybe belongs in mathlib?
lemma Finset.subtype_union {α} (p : α → Prop) [DecidableEq α] [DecidablePred p] (s1 s2 : Finset α) :
    Finset.subtype p (s1 ∪ s2) = Finset.subtype p s1 ∪ Finset.subtype p s2 := by
  ext a; simp

lemma Finset.subtype_map_subtype {α : Type} {p : α → Prop} [DecidablePred p]
    (x : Finset {a : α // p a}) :
    Finset.subtype p (Finset.map (Function.Embedding.subtype p) x) = x := by
  ext ⟨y, hy⟩
  simp [hy]

lemma lemma1 {α : Type} [Fintype α] [DecidableEq α] (s : α) :
   Fintype.card {a : Finset α // s ∈ a} = Fintype.card {a : Finset α // s ∉ a} := by
  let b : {a : Finset α // s ∉ a} → {a : Finset α // s ∈ a} :=
     fun ⟨a, ha⟩ ↦ ⟨Finset.cons s a ha, Finset.mem_cons_self s a⟩
  have hb : b.Bijective := by
    constructor
    · rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
      simp only [Subtype.mk.injEq, b] at hxy
      rw [Subtype.mk.injEq]
      apply_fun (Finset.erase · s) at hxy
      simp [Finset.erase_eq_of_notMem hx, Finset.erase_eq_of_notMem hy] at hxy
      exact hxy
    · rintro ⟨x, hx⟩
      use ⟨x.erase s, Finset.notMem_erase s x⟩
      simp [Finset.insert_erase hx, b]
  rw [Fintype.card_of_bijective hb]

lemma usa2002_p1_generalized
    {α : Type} [DecidableEq α] [Fintype α] (n : ℕ) (hs : Fintype.card α = n)
    (N : ℕ) (hN : N ≤ 2 ^ n) :
    ∃ f : Finset α → Color,
      ((∀ s1 s2 : Finset α, f s1 = f s2 → f (s1 ∪ s2) = f s1) ∧
       (Fintype.card { a : Finset α // f a = Color.red } = N)) := by
  -- Informal solution from
  -- https://artofproblemsolving.com/wiki/index.php/2002_USAMO_Problems/Problem_1
  -- Let a set colored in such a manner be called *properly colored*.
  -- We prove that any set with n elements can be properly colored for any
  -- 0 ≤ N ≤ 2ⁿ. We proceed by induction.

  revert N α
  induction' n with k ih
  · -- The base case, n = 0, is trivial.
    intro α hde hft hs N hN
    rw [Nat.pow_zero] at hN
    interval_cases N
    · use λ _ ↦ Color.blue
      simp only [reduceCtorEq, forall_true_left, forall_const, Fintype.card_eq_zero,
                 and_self]
    · use λ _ ↦ Color.red
      simp [Fintype.card_subtype, Finset.card_univ, hs]
  · -- Suppose that our claim holds for n = k. Let s ∈ S, |S| = k + 1,
    -- and let S' denote the set of all elements of S other than s.
    intros S hde hft hs N hN
    have s : S := Nonempty.some (Fintype.card_pos_iff.mp (Nat.lt_of_sub_eq_succ hs))
    let S' := { a : S // a ≠ s }
    have hs' : Fintype.card S' = k := by simp [Fintype.card_subtype_compl, hs, S']

    obtain hl | hg := le_or_gt N (2 ^ k)
    · -- If N ≤ 2ᵏ, then we may color blue all subsets of S which contain s,
      -- and we may properly color S'. This is a proper coloring because the union
      -- of any two red sets must be a subset of S', which is properly colored, and
      -- any the union of any two blue sets either must be in S', which is properly
      -- colored, or must contain s and therefore be blue.
      obtain ⟨f', hf1', hf2'⟩ := ih hs' N hl
      let f (x: Finset S) : Color :=
        if s ∈ x then Color.blue else f' (Finset.subtype _ x)
      use f
      have h2 : ∀ a : Finset S,
                (f a = Color.red ↔ s ∉ a ∧ f' (Finset.subtype _ a) = Color.red) := by
        intro a
        constructor
        · intro ha
          have haa : s ∉ a := by
            intro hns
            simp [hns, f] at ha
          simp only [haa, f] at ha
          exact ⟨haa, ha⟩
        · intro hsa
          simp [hsa, f]
      constructor
      · intro s1 s2 hs12
        obtain ⟨h4, _⟩ := h2 s1
        obtain ⟨h4', _⟩ := h2 s2
        obtain hfs1 | hfs1 := Classical.em (f s1 = Color.red)
        · obtain ⟨h6, h7⟩ := h4 hfs1
          have hfs2 : f s2 = Color.red := by rwa [hs12] at hfs1
          obtain ⟨h6', h7'⟩ := h4' hfs2
          rw [←h7] at h7'
          have h8 := hf1' _ _ h7'
          simp [hs12, h6, h6', f]
          rw [Finset.subtype_union, Finset.union_comm]
          rw [h7'] at h8
          convert h8
        · obtain hss | hss := Classical.em (s ∈ s1 ∪ s2)
          · unfold f
            simp only [Finset.mem_union] at hss
            simp only [Finset.mem_union, hss, dite_eq_ite, ite_true]
            cases' hss with hss hss
            · simp [hss]
            · split_ifs with h
              · rfl
              · simp only [h, dite_eq_ite, f] at hfs1
                match h20 : (f' (Finset.subtype (fun a => ¬a = s) s1)) with
                | Color.red => exact (hfs1 h20).elim
                | Color.blue => rfl
          · -- s1 ∪ s2 is in S'
            simp only [hss, f]
            rw [Finset.mem_union, not_or] at hss
            simp only [hss.1, dite_false]
            rw [Finset.subtype_union]
            apply hf1'
            · simp [hss.1, hss.2, f] at hs12
              exact hs12

      · let b : { a : Finset S // f a = Color.red } → { a : Finset S' // f' a = Color.red } :=
            fun ⟨a, ha⟩ ↦ ⟨Finset.subtype _ a, by
               simp only [f] at ha
               split_ifs at ha
               exact ha
              ⟩

        have h3 : Function.Bijective b := by
          constructor
          · rintro ⟨x, hx⟩ ⟨y,hy⟩ hxy
            unfold b at hxy
            simp at hxy
            obtain ⟨h3, _⟩ := (h2 x).mp hx
            obtain ⟨h4, _⟩ := (h2 y).mp hy
            apply_fun (Finset.map (Function.Embedding.subtype _) ·) at hxy
            have h3' : ∀ x1 ∈ x, x1 ≠ s := by
              intro x1 hx1 hx1n; rw [hx1n] at hx1; exact h3 hx1
            have h4' : ∀ y1 ∈ y, y1 ≠ s := by
              intro y1 hy1 hy1n; rw [hy1n] at hy1; exact h4 hy1
            rw [Finset.subtype_map_of_mem h3',
                Finset.subtype_map_of_mem h4'] at hxy
            exact SetCoe.ext hxy
          · rintro ⟨x, hx⟩
            use ⟨Finset.map (Function.Embedding.subtype _) x,
                 by simp [Finset.subtype_map_subtype, hx, f]⟩
            simp only [b, Subtype.mk.injEq]
            exact Finset.subtype_map_subtype x
        rw [Fintype.card_of_bijective h3]
        exact hf2'
    · -- If N > 2ᵏ, then we color all subsets containing s red, and we color
      -- N - 2ᵏ elements of S' red in such a way that S' is colored properly.
      -- Then S is properly colored, using similar reasoning as before.
      -- Thus the induction is complete.
      have hl : N - 2^k ≤ 2^k := by
        rw [pow_succ', two_mul] at hN
        exact Nat.sub_le_of_le_add hN
      obtain ⟨f', hf1', hf2'⟩ := ih hs' (N - 2^k) hl
      let f (x : Finset S) : Color :=
        if s ∈ x then Color.red else f' (Finset.subtype _ x)
      use f
      have h2 : ∀ a : Finset S,
          (f a = Color.blue ↔ s ∉ a ∧ f' (Finset.subtype _ a) = Color.blue) := by
        intro a
        constructor
        · intro ha
          have haa : s ∉ a := fun hns ↦ by simp [hns, f] at ha
          simp only [haa, f] at ha
          exact ⟨haa, ha⟩
        · intro hsa
          simp [hsa, f]
      constructor
      · intro s1 s2 hs12
        obtain ⟨h4, _⟩ := h2 s1
        obtain ⟨h4', _⟩ := h2 s2
        obtain hfs1 | hfs1 := Classical.em (f s1 = Color.blue)
        · obtain ⟨h6, h7⟩ := h4 hfs1
          have hfs2 : f s2 = Color.blue := by rwa [hs12] at hfs1
          obtain ⟨h6', h7'⟩ := h4' hfs2
          rw [←h7] at h7'
          have h8 := hf1' _ _ h7'
          simp (config := {decide := true}) only [hs12, Finset.mem_union, h6, h6', f]
          rw [Finset.subtype_union, Finset.union_comm]
          simp (config := { decide := true }) only [↓reduceIte, ne_eq]
          rw [h7'] at h8
          convert h8
        · obtain hss | hss := Classical.em (s ∈ s1 ∪ s2)
          · unfold f
            simp only [Finset.mem_union] at hss
            simp only [Finset.mem_union, hss, dite_eq_ite, ite_true]
            cases' hss with hss hss
            · simp [hss]
            · split_ifs with h
              · rfl
              · simp only [h, f] at hfs1
                match h20 : (f' (Finset.subtype (fun a => ¬a = s) s1)) with
                | Color.blue => exact (hfs1 h20).elim
                | Color.red => rfl
          · -- s1 ∪ s2 is in S'
            simp only [hss, dite_false, f, S']
            rw [Finset.mem_union, not_or] at hss
            simp only [hss.1, Finset.subtype_union, ite_false]
            apply hf1'
            · simp only [hss.1, hss.2, f, S'] at hs12
              exact hs12
      · have h2' : ∀ (a : Finset S),
            f a = Color.red ↔ s ∈ a ∨
                 f' (Finset.subtype (fun a => a ≠ s) a) = Color.red := by
          intro a
          simp only [ne_eq, dite_eq_ite, ite_eq_left_iff, f, S']
          tauto
        let b : { a // f a = Color.red } →
               { a : Finset S // s ∈ a } ⊕ { a' // f' a' = Color.red } :=
          fun ⟨a, ha⟩ ↦
            if h : s ∈ a
            then Sum.inl ⟨a, h⟩
            else Sum.inr ⟨Finset.subtype _ a, by
              match (h2' a).mp ha with
              | .inl h' => contradiction
              | .inr hh => exact hh ⟩

        have h3 : Function.Bijective b := by
          constructor
          · rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
            simp only [dite_eq_ite, S', b] at hxy
            split_ifs at hxy with h4 h5 h6
            · simp at hxy; exact SetCoe.ext hxy
            · simp only [Sum.inr.injEq, Subtype.mk.injEq] at hxy
              cases' (h2' x).mp hx with hxx hxx
              · contradiction
              · rw [Finset.ext_iff] at hxy
                cases' (h2' y).mp hy with hyy hyy
                · contradiction
                · simp only [Finset.mem_subtype, Subtype.forall] at hxy
                  rw [Subtype.mk.injEq]
                  ext a
                  constructor
                  · intro ha
                    have h6 : ¬ a = s := by intro has; rw [has] at ha; contradiction
                    rwa [←hxy a h6]
                  · intro ha
                    have h6 : ¬ a = s := by intro has; rw [has] at ha; contradiction
                    rwa [hxy a h6]
          · intro x
            match x with
            | .inl ⟨y, hy⟩ =>
              have h5 : f y = Color.red := if_pos hy
              use ⟨y, h5⟩
              simp only [ne_eq, dite_eq_ite, hy, dite_true, b]
            | .inr ⟨y, hy⟩ =>
              use ⟨Finset.map (Function.Embedding.subtype _) y,
                  by simp [Finset.subtype_map_subtype, hy, b, f]⟩
              simp [Finset.subtype_map_subtype, b, f]
        rw [Fintype.card_of_bijective h3]
        have h4 : Fintype.card { a : Finset S // s ∈ a } = 2^k := by
          clear h3 b h2' h2 f hf2' hf1'
          have h5 : Fintype.card (Finset S') = 2 ^ k := by rw [Fintype.card_finset, hs']
          rw [lemma1]
          let b : Finset S' → { a : Finset S // s ∉ a } :=
            fun a ↦ ⟨Finset.map (Function.Embedding.subtype _) a, by simp⟩
          have hb : b.Bijective := by
            constructor
            · rintro x y hxy
              simp only [Subtype.mk.injEq, Finset.map_inj, b] at hxy
              exact hxy
            · rintro ⟨x, hx⟩
              use Finset.subtype _ x
              simp only [Finset.subtype_map, Subtype.mk.injEq, b]
              have h7 : ∀ a ∈ x, ¬ a = s := by
                intro a ha has
                rw [has] at ha
                contradiction
              exact Finset.filter_eq_self.mpr h7
          rw [←Fintype.card_of_bijective hb]
          exact h5

        simp only [Fintype.card_sum, h4, hf2']
        rw [add_tsub_cancel_iff_le]
        exact Nat.le_of_lt hg

snip end

problem usa2002_p1
    {α : Type} [DecidableEq α] [Fintype α] (hs : Fintype.card α = 2002)
    (N : ℕ) (hN : N ≤ 2 ^ 2002) :
    ∃ f : Finset α → Color,
      ((∀ s1 s2 : Finset α, f s1 = f s2 → f (s1 ∪ s2) = f s1) ∧
       (Fintype.card
           { a : Finset α // f a = Color.red } = N)) := by
  exact usa2002_p1_generalized 2002 hs N hN


end Usa2002P1
