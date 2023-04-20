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
  induction n with
  | zero => use ∅; simp
  | succ n ih =>
    obtain ⟨Sp, sp_nonnegative, sp_card, hsp⟩ := ih
    let L : ℤ := ∏ s in Sp, ∏ t in Sp.erase s, (s-t)^2

    have all_terms_pos :
      ∀ s ∈ Sp, ∀ t ∈ Sp.erase s, 0 < (s-t)^2 := by
          intros s _hs t ht
          obtain ⟨t_ne_s, _⟩ := Finset.mem_erase.mp ht
          have : s - t ≠ 0 := sub_ne_zero_of_ne t_ne_s.symm
          positivity

    have inner_prod_pos :
      ∀ s ∈ Sp, 0 < ∏ t in Sp.erase s, (s-t)^2 := by
        intros s hs
        exact Finset.prod_pos (all_terms_pos s hs)

    have L_pos : 0 < L := Finset.prod_pos inner_prod_pos

    -- Define Sₙ₊₁ = { L + a : a ∈ Sₙ } ∪ { 0 }.
    let S : Finset ℤ := Sp.map (addLeftEmbedding L) ∪ {0}
    use S

    constructor
    · -- all elements are nonnegative
      intros x hx
      rw[Finset.mem_union] at hx
      cases hx with
      | inl hx =>
        rw[Finset.mem_map] at hx
        obtain ⟨w, hw1, hw2⟩ := hx
        have := sp_nonnegative w hw1
        replace hw2 : L + w = x := hw2
        linarith
      | inr hx => simp_all
    · constructor
      · --cardinality is n + 1
        have hdisj : Disjoint (Finset.map (addLeftEmbedding L) Sp) {0} := by
          intros X hX h0 y hy
          have hyy := h0 hy
          rw[Finset.mem_singleton] at hyy
          rw[hyy] at hy
          have hxx := hX hy
          rw[Finset.mem_map] at hxx
          obtain ⟨z, hz, hz2⟩ := hxx
          replace hz2 : L + z = 0 := hz2
          have := sp_nonnegative z hz
          linarith
        rw[Finset.card_disjoint_union hdisj, Finset.card_singleton,
           Finset.card_map, sp_card]
      · intros α hα β hβ α_ne_β
        rw[Finset.mem_union, Finset.mem_map] at hα hβ
        -- If α,β ∈ Sₙ₊₁ and either α or β is zero, then (α - β)² divides αβ.
        cases hα with
        | inr hα => simp_all
        | inl hα =>
          cases hβ with
          | inr hβ => simp_all
          | inl hβ =>
            obtain ⟨a, ha, ha2⟩ := hα
            replace ha2 : L + a = α := ha2
            obtain ⟨b, hb, hb2⟩ := hβ
            replace hb2 : L + b = β := hb2
            have a_ne_b : a ≠ b := by aesop
            have ih := hsp a ha b hb a_ne_b
            have h5 : L = (∏ t in Sp.erase a, (a-t)^2) *
                         ∏ s in Sp.erase a, ∏ t in Sp.erase s, (s-t)^2 :=
              (Finset.mul_prod_erase Sp _ ha).symm
            have hbb := Finset.mem_erase.mpr ⟨a_ne_b.symm, hb⟩
            have h6 : (a-b)^2 * ∏ t in (Sp.erase a).erase b, (a-t)^2 =
                      ∏ t in Sp.erase a, (a-t)^2 :=
               Finset.mul_prod_erase (Sp.erase a) (fun x ↦ (a-x)^2) hbb
            have Lmod : L % (a - b)^2 = 0 := by
                 rw[h5, ←h6, mul_assoc, Int.mul_emod, Int.emod_self]
                 norm_num
            have Lmod' : (L + a) * (L + b) % (a-b)^2 = 0 := by
               have h7 : (L + a) * (L + b) = L * (L + a + b) + a * b := by ring
               rw[h7]
               rw[Int.add_emod]
               have h8 : L * (L + a + b) % (a - b) ^ 2 = 0 := by
                 rw[Int.mul_emod, Lmod]
                 norm_num
               have h9 :  a * b % (a - b) ^ 2 = 0 := Int.emod_eq_zero_of_dvd ih
               rw[h8, h9]
               norm_num
            have hab : a-b = α - β := by linarith
            rw[ha2, hb2, hab] at Lmod'
            exact Int.dvd_of_emod_eq_zero Lmod'

theorem usa1998_q5 (n : ℕ) (_hn : 2 ≤ n) :
    ∃ S : Finset ℤ,
       S.card = n ∧
       ∀ a ∈ S, ∀ b ∈ S, a ≠ b → (a - b)^2 ∣ a * b := by
  obtain ⟨S, _, hS⟩ := usa1998_q5_stronger n
  exact ⟨S, hS⟩
