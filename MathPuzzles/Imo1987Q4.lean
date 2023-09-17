/-
Copyright (c) 2023 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Aesop
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Interval
import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Ring

import MathPuzzles.Meta.ProblemExtraction

#[problem_setup]/-!
# International Mathematical Olympiad 1987, Problem 4

Prove that there is no function f : ℕ → ℕ such that f(f(n)) = n + 1987
for every n.
-/

#[problem_setup] namespace Imo1987Q4

lemma subset_finite {A B : Set ℕ} (h : A ⊆ B) (hab : Finite ↑B) : Finite ↑A := by
  rw[Set.finite_coe_iff]
  rw[Set.finite_coe_iff] at hab
  exact Set.Finite.subset hab h

lemma subset_fintype {A B : Set ℕ} (h : A ⊆ B) (hab : Fintype ↑B) : Fintype ↑A := by
  exact @Fintype.ofFinite A (subset_finite h (Finite.of_fintype ↑B))

/--
More general version of the problem.
-/
theorem imo1987_q4_generalized (m : ℕ) :
    (¬∃ f : ℕ → ℕ, ∀ n, f (f n) = n + (2 * m + 1)) := by
  -- Informal solution by Sawa Pavlov, listed at
  -- https://artofproblemsolving.com/wiki/index.php/1987_IMO_Problems/Problem_4

  intro hf
  obtain ⟨f, hf⟩ := hf

  -- Note that f is injective, because if f(n) = f(m),
  -- then f(f(n)) = f(f(m)), so m = n.
  have f_injective : f.Injective := by
    intros n m hnm; have hfn := hf n; simp_all only [add_left_inj]

  -- Let A := ℕ - f(ℕ) and B := f(A).
  let NN : Set ℕ := Set.univ
  let A : Set ℕ := NN \ (f '' NN)
  let B : Set ℕ := f '' A

  have hid := Set.image_diff f_injective NN (f '' NN)
  rw[show f '' (NN \ f '' NN) = B by rfl] at hid

  -- A and B are disjoint and have union ℕ - f(f(ℕ)).
  have ab_disjoint : Disjoint A B := by
    intros _C hca hcb c hc
    exact Set.not_mem_of_mem_diff (hca hc) (Set.image_subset f sdiff_le (hcb hc))

  have ab_union : A ∪ B = NN \ (f '' (f '' NN)) := by
    rw[hid]
    apply Set.eq_of_subset_of_subset
    · intros x hx
      cases hx <;> aesop
    · intros x hx
      obtain ⟨_hx, hx'⟩ := hx
      cases Classical.em (x ∈ A) <;> aesop

  -- ... which is {0, 1, ... , 2 * m}.
  have ab_range : A ∪ B = {n | n < 2*m + 1} := by
    apply Set.eq_of_subset_of_subset
    · rw[ab_union]
      intros x hx
      simp at hx
      simp
      by_contra H
      push_neg at H
      have hz: ∃ z, x = (2 * m + 1) + z := exists_add_of_le H
      obtain ⟨z, hz⟩ := hz
      rw[hz] at hx
      have hzz := hx z
      rw[hf z, add_comm] at hzz
      exact (hzz rfl).elim
    · rw[ab_union]
      intros x hx
      aesop

  -- But since f is injective they have the
  -- same number of elements, which is impossible since {0, 1, ... , 2 * m}
  -- has an odd number of elements.

  have ab_fintype : Fintype ↑(A ∪ B) := by rw[ab_range]; exact inferInstance

  have h2 : Fintype.card ↑(A ∪ B) = 2 * m + 1 := by
    have hc := @Fintype.card_congr' ↑(A ∪ B)
                  {x | x < 2 * m + 1} _ _ (by rw[ab_range])
    simp only [hc, Fintype.card_ofFinset, Finset.card_range]

  have a_fintype := subset_fintype (Set.subset_union_left A B) ab_fintype
  have b_fintype := subset_fintype (Set.subset_union_right A B) ab_fintype
  have h3 := @Set.toFinset_union ℕ A B _ a_fintype b_fintype ab_fintype
  rw[←@Set.toFinset_card _ (A ∪ B) ab_fintype] at h2
  rw[h3] at h2; clear h3
  have ab_disjoint' :=
    (@Set.disjoint_toFinset _ _ _ a_fintype b_fintype).mpr ab_disjoint
  rw[Finset.card_disjoint_union ab_disjoint'] at h2
  rw[Set.toFinset_card, Set.toFinset_card] at h2
  rw[Set.card_image_of_injective A f_injective] at h2
  ring_nf at h2
  apply_fun (· % 2) at h2
  norm_num at h2

problem imo1987_q4 : (¬∃ f : ℕ → ℕ, ∀ n, f (f n) = n + 1987) := by
  rw[show 1987 = (2 * 993 + 1) by norm_num]
  exact imo1987_q4_generalized 993
