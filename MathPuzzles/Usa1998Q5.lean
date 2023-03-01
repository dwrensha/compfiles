import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.BigOperators.Order
import Mathlib.Data.Int.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# USA Mathematical Olympiad 1998, Problem 5

Prove that for each n ≥ 2, there is a set S of n integers such that
(a-b)² divides ab for every distinct a,b ∈ S.
-/

namespace Usa1998Q5

open BigOperators

lemma usa1998_q5_stronger (n : ℕ) :
    ∃ S : Finset ℤ,
       (∀ x ∈ S, 0 ≤ x) ∧
       S.card = n ∧
       ∀ a ∈ S, ∀ b ∈ S, a ≠ b → (a - b)^2 ∣ a * b := by
  -- (Adapation of informal proof from Andreescu & Feng.)
  -- We will prove by induction on n that we can find such a set Sₙ all
  -- of whose elements are nonnegative.
  induction n with
  | zero => use ∅; simp
  | succ n ih =>
    obtain ⟨Sp, sp_nonnegative, sp_card, hsp⟩ := ih
    -- Now suppose that for some n, the desired set Sₙ of n nonegative
    -- integers exists. Let L be the product of those numbers
    -- (a-b)² and ab that are nonzero, with (a,b) ranging over pairs of
    -- distinct elements from Sₙ.

    let L : ℤ := ∏ s in Sp.erase 0,
                   ∏ t in (Sp.erase 0).erase s, s*t*(s-t)^2

    have all_terms_pos :
      ∀ s ∈ Sp.erase 0,
        ∀ t ∈ (Sp.erase 0).erase s, 0 < s*t*(s-t)^2 := by
          intros s hs t ht
          obtain ⟨s_ne_zero, h3⟩ := Finset.mem_erase.mp hs
          have hsn := sp_nonnegative s h3
          obtain ⟨t_ne_s, h4'⟩ := (Finset.mem_erase.mp ht)
          obtain ⟨t_ne_zero, h4⟩ := Finset.mem_erase.mp h4'
          have htn := sp_nonnegative t h4
          have hsz : 0 < s := Ne.lt_of_le s_ne_zero.symm hsn
          have htz : 0 < t := Ne.lt_of_le t_ne_zero.symm htn
          have : s - t ≠ 0 := sub_ne_zero_of_ne t_ne_s.symm
          positivity

    have inner_prod_pos :
      ∀ s ∈ Sp.erase 0,
        0 < ∏ t in (Sp.erase 0).erase s, s*t*(s-t)^2 := by
          intros s hs
          exact Finset.prod_pos (all_terms_pos s hs)

    have L_pos : 0 < L := Finset.prod_pos inner_prod_pos
    have L_nonneg : 0 ≤ L := le_of_lt L_pos

    -- Define
    --   Sₙ₊₁ = { L + a : a ∈ Sₙ } ∪ { 0 }.

    let S : Finset ℤ := Sp.map (addLeftEmbedding L) ∪ {0}
    use S

    -- Then Sₙ₊₁ consists of n + 1 nonnegative integers, since L > 0.
    constructor
    · intros x hx
      rw[Finset.mem_union] at hx
      cases hx with
      | inl hx => sorry/-
        rw[Finset.mem_map] at hx
        obtain ⟨w, hw1, hw2⟩ := hx
        have := sp_nonnegative w hw1
        replace hw2 : L + w = x := hw2
        linarith-/
      | inr hx => simp_all
    · constructor
      · have hdisj : Disjoint (Finset.map (addLeftEmbedding L) Sp) {0} := by
             sorry/-
             intros X hX h0 y hy
             have hyy := h0 hy
             rw[Finset.mem_singleton] at hyy
             rw[hyy] at hy
             have hxx := hX hy
             rw[Finset.mem_map] at hxx
             obtain ⟨z, hz, hz2⟩ := hxx
             replace hz2 : L + z = 0 := hz2
             have := sp_nonnegative z hz
             clear hX h0 -- Finset ≤ relation confuses linarith
             linarith-/
        rw[Finset.card_disjoint_union hdisj, Finset.card_singleton,
           Finset.card_map, sp_card]
      · intros α hα β hβ α_ne_β
        rw[Finset.mem_union, Finset.mem_map] at hα hβ
        -- If α,β ∈ Sₙ₊₁ and either α or β is zero, then (α - β)² divides αβ.
        cases hα with
        | inr hα => sorry --simp_all
        | inl hα =>
          cases hβ with
          | inr hβ => sorry --simp_all
          | inl hβ =>
            obtain ⟨a, ha, ha2⟩ := hα
            replace ha2 : L + a = α := ha2
            obtain ⟨b, hb, hb2⟩ := hβ
            replace hb2 : L + b = β := hb2
            have a_ne_b : a ≠ b := by aesop
            have ih := hsp a ha b hb a_ne_b
            sorry

    -- If L + a, L + b ∈ Sₙ₊₁, with a,b distinct elements of Sₙ, then
    --   (L + a)(L + b) ≡ ab ≡ 0 (mod (a - b)²),
    -- so [(L + a) - (L + b)]² divides (L + a)(L + b), completing the inductive
    -- step.


theorem usa1998_q5 (n : ℕ) (_hn : 2 ≤ n) :
    ∃ S : Finset ℤ,
       S.card = n ∧
       ∀ a ∈ S, ∀ b ∈ S, a ≠ b → (a - b)^2 ∣ a * b := by
  obtain ⟨S, _, hS⟩ := usa1998_q5_stronger n
  exact ⟨S, hS⟩
