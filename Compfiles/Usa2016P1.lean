/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Powerset
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics] }

/-!
# USA Mathematical Olympiad 2016, Problem 1

Let X₁, X₂, …, X₁₀₀ be a sequence of mutually distinct nonempty subsets of a set S.
Any two sets Xᵢ and Xᵢ₊₁ are disjoint and their union is not the whole set S,
that is, Xᵢ ∩ Xᵢ₊₁ = ∅ and Xᵢ ∪ Xᵢ₊₁ ≠ S, for all i ∈ {1, …, 99}.
Find the smallest possible number of elements in S.
-/

namespace Usa2016P1

open Finset

/-- `HasChain n` means that an `n`-element set (which we may take to be `Fin n`)
admits a sequence of 100 mutually distinct nonempty subsets in which any two
consecutive sets are disjoint and do not cover the whole set. -/
def HasChain (n : ℕ) : Prop :=
  ∃ X : Fin 100 → Finset (Fin n),
    (∀ i, (X i).Nonempty) ∧
      (∀ i j, X i = X j → i = j) ∧
        ∀ i : Fin 99, Disjoint (X i.castSucc) (X i.succ) ∧
          X i.castSucc ∪ X i.succ ≠ univ

snip begin

/-- An explicit chain of 100 subsets of an 8-element set.
(Obtained from the inductive construction of the official solution:
start from the chain `34, 1, 23, 4, 12, 3, 14, 2, 13` on a 4-element set and
repeatedly duplicate the chain, glue the two copies together with the empty set
in between, and insert a new element into alternating positions.) -/
def witness : Fin 100 → Finset (Fin 8) := ![
  {2, 3, 4, 5, 6, 7},
  {0},
  {1, 2, 4, 5, 6, 7},
  {3},
  {0, 1, 4, 5, 6, 7},
  {2},
  {0, 3, 4, 5, 6, 7},
  {1},
  {4, 5, 6, 7},
  {2, 3},
  {0, 4, 5, 6, 7},
  {1, 2},
  {3, 4, 5, 6, 7},
  {0, 1},
  {2, 4, 5, 6, 7},
  {0, 3},
  {5, 6, 7},
  {2, 3, 4},
  {0, 5, 6, 7},
  {1, 2, 4},
  {3, 5, 6, 7},
  {0, 1, 4},
  {2, 5, 6, 7},
  {0, 3, 4},
  {1, 5, 6, 7},
  {4},
  {2, 3, 5, 6, 7},
  {0, 4},
  {1, 2, 5, 6, 7},
  {3, 4},
  {0, 1, 5, 6, 7},
  {2, 4},
  {6, 7},
  {2, 3, 4, 5},
  {0, 6, 7},
  {1, 2, 4, 5},
  {3, 6, 7},
  {0, 1, 4, 5},
  {2, 6, 7},
  {0, 3, 4, 5},
  {1, 6, 7},
  {4, 5},
  {2, 3, 6, 7},
  {0, 4, 5},
  {1, 2, 6, 7},
  {3, 4, 5},
  {0, 1, 6, 7},
  {2, 4, 5},
  {0, 3, 6, 7},
  {5},
  {2, 3, 4, 6, 7},
  {0, 5},
  {1, 2, 4, 6, 7},
  {3, 5},
  {0, 1, 4, 6, 7},
  {2, 5},
  {0, 3, 4, 6, 7},
  {1, 5},
  {4, 6, 7},
  {2, 3, 5},
  {0, 4, 6, 7},
  {1, 2, 5},
  {3, 4, 6, 7},
  {0, 1, 5},
  {7},
  {2, 3, 4, 5, 6},
  {0, 7},
  {1, 2, 4, 5, 6},
  {3, 7},
  {0, 1, 4, 5, 6},
  {2, 7},
  {0, 3, 4, 5, 6},
  {1, 7},
  {4, 5, 6},
  {2, 3, 7},
  {0, 4, 5, 6},
  {1, 2, 7},
  {3, 4, 5, 6},
  {0, 1, 7},
  {2, 4, 5, 6},
  {0, 3, 7},
  {5, 6},
  {2, 3, 4, 7},
  {0, 5, 6},
  {1, 2, 4, 7},
  {3, 5, 6},
  {0, 1, 4, 7},
  {2, 5, 6},
  {0, 3, 4, 7},
  {1, 5, 6},
  {4, 7},
  {2, 3, 5, 6},
  {0, 4, 7},
  {1, 2, 5, 6},
  {3, 4, 7},
  {0, 1, 5, 6},
  {2, 4, 7},
  {6},
  {2, 3, 4, 5, 7},
  {0, 6}]

/-- The explicit witness verifies that `HasChain 8` holds. -/
lemma hasChain_eight : HasChain 8 :=
  ⟨witness, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- Any chain on an `n`-element set uses at most `2 ^ n - 1` nonempty subsets,
so `n ≤ 6` is impossible since `2 ^ 6 - 1 < 100`. -/
lemma not_hasChain_of_le_six {n : ℕ} (hn : n ≤ 6) : ¬ HasChain n := by
  classical
  rintro ⟨X, hne, hinj, -⟩
  have himg : (univ : Finset (Fin 100)).image X ⊆ univ.erase (∅ : Finset (Fin n)) := by
    intro t ht
    rw [mem_image] at ht
    obtain ⟨i, -, rfl⟩ := ht
    rw [mem_erase]
    exact ⟨nonempty_iff_ne_empty.mp (hne i), mem_univ _⟩
  have hcard_image : ((univ : Finset (Fin 100)).image X).card = 100 := by
    rw [card_image_of_injective _ hinj, card_univ, Fintype.card_fin]
  have hcard_erase : (univ.erase (∅ : Finset (Fin n))).card = 2 ^ n - 1 := by
    rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_finset, Fintype.card_fin]
  have hle := card_le_card himg
  rw [hcard_image, hcard_erase] at hle
  have hpow : 2 ^ n ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) hn
  omega

/-- The main combinatorial estimate: no chain exists on a 7-element set.
Sets of size at least 4 must be preceded by sets of size at most 2, and there
are only 28 nonempty subsets of size at most 2 and 35 subsets of size 3, so a
chain on 7 elements has length at most `28 + 35 + (28 + 1) = 92 < 100`. -/
lemma not_hasChain_seven : ¬ HasChain 7 := by
  classical
  rintro ⟨X, hne, hinj, hchain⟩
  -- Consecutive sets have total size at most 6.
  have hsum : ∀ i : Fin 99, (X i.castSucc).card + (X i.succ).card ≤ 6 := by
    intro i
    obtain ⟨hdisj, hne_univ⟩ := hchain i
    have hss : X i.castSucc ∪ X i.succ ⊂ univ := ssubset_univ_iff.mpr hne_univ
    have hlt : (X i.castSucc ∪ X i.succ).card < 7 := by
      have h2 := card_lt_card hss
      simpa using h2
    rw [card_union_of_disjoint hdisj] at hlt
    omega
  -- The indices, split by the size of the corresponding set.
  let A : Finset (Fin 100) := univ.filter fun i => (X i).card ≤ 2
  let B : Finset (Fin 100) := univ.filter fun i => (X i).card = 3
  let C : Finset (Fin 100) := univ.filter fun i => 4 ≤ (X i).card
  have hdisj_AB : Disjoint A B := by
    simp only [A, B, disjoint_filter]
    intro i _ h1 h2
    omega
  have hdisj_AC : Disjoint A C := by
    simp only [A, C, disjoint_filter]
    intro i _ h1 h2
    omega
  have hdisj_BC : Disjoint B C := by
    simp only [B, C, disjoint_filter]
    intro i _ h1 h2
    omega
  have hunion : A ∪ B ∪ C = univ := by
    ext i
    simp only [A, B, C, mem_union, mem_filter, mem_univ, true_and, iff_true]
    omega
  have hpart : A.card + B.card + C.card = 100 := by
    have h1 : (A ∪ B ∪ C).card = A.card + B.card + C.card := by
      rw [card_union_of_disjoint (disjoint_union_left.mpr ⟨hdisj_AC, hdisj_BC⟩),
        card_union_of_disjoint hdisj_AB]
    rw [hunion, card_univ, Fintype.card_fin] at h1
    omega
  -- There are only 28 nonempty subsets of size at most 2.
  have hA : A.card ≤ 28 := by
    have himg : A.image X ⊆ powersetCard 1 univ ∪ powersetCard 2 univ := by
      intro t ht
      rw [mem_image] at ht
      obtain ⟨i, hi, rfl⟩ := ht
      simp only [A, mem_filter, mem_univ, true_and] at hi
      have hpos : 0 < (X i).card := card_pos.mpr (hne i)
      have h12 : (X i).card = 1 ∨ (X i).card = 2 := by omega
      rw [mem_union, mem_powersetCard, mem_powersetCard]
      rcases h12 with h | h
      · exact Or.inl ⟨subset_univ _, h⟩
      · exact Or.inr ⟨subset_univ _, h⟩
    have hdisj12 : Disjoint (powersetCard 1 (univ : Finset (Fin 7)))
        (powersetCard 2 univ) := by
      rw [disjoint_left]
      intro x hx1 hx2
      rw [mem_powersetCard] at hx1 hx2
      omega
    have hcard : (powersetCard 1 (univ : Finset (Fin 7)) ∪ powersetCard 2 univ).card = 28 := by
      rw [card_union_of_disjoint hdisj12, card_powersetCard, card_powersetCard, card_univ,
        Fintype.card_fin]
      decide
    calc A.card = (A.image X).card := (card_image_of_injective A hinj).symm
      _ ≤ (powersetCard 1 (univ : Finset (Fin 7)) ∪ powersetCard 2 univ).card :=
          card_le_card himg
      _ = 28 := hcard
  -- There are only 35 subsets of size 3.
  have hB : B.card ≤ 35 := by
    have himg : B.image X ⊆ powersetCard 3 univ := by
      intro t ht
      rw [mem_image] at ht
      obtain ⟨i, hi, rfl⟩ := ht
      simp only [B, mem_filter, mem_univ, true_and] at hi
      rw [mem_powersetCard]
      exact ⟨subset_univ _, hi⟩
    have hcard : (powersetCard 3 (univ : Finset (Fin 7))).card = 35 := by
      rw [card_powersetCard, card_univ, Fintype.card_fin]
      decide
    calc B.card = (B.image X).card := (card_image_of_injective B hinj).symm
      _ ≤ (powersetCard 3 (univ : Finset (Fin 7))).card := card_le_card himg
      _ = 35 := hcard
  -- Every set of size at least 4 (except possibly the first one) is preceded by
  -- a set of size at most 2, and this predecessor map is injective.
  have hC : C.card ≤ A.card + 1 := by
    have hpred : (C.erase 0).card ≤ A.card := by
      apply card_le_card_of_injOn
        (f := fun i : Fin 100 => ⟨i.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩)
      · intro i hi
        rw [mem_coe, mem_erase] at hi
        obtain ⟨hi0, hiC⟩ := hi
        simp only [C, mem_filter, mem_univ, true_and] at hiC
        obtain ⟨k, rfl⟩ := Fin.eq_zero_or_eq_succ i |>.resolve_left hi0
        have hsumk := hsum k
        rw [mem_coe, mem_filter]
        refine ⟨mem_univ _, ?_⟩
        show (X k.castSucc).card ≤ 2
        omega
      · intro i hi j hj hij
        rw [mem_coe, mem_erase] at hi hj
        have h2 : i.val - 1 = j.val - 1 := congrArg Fin.val hij
        have hi1 : 1 ≤ i.val := Nat.one_le_iff_ne_zero.mpr fun h => hi.1 (Fin.ext h)
        have hj1 : 1 ≤ j.val := Nat.one_le_iff_ne_zero.mpr fun h => hj.1 (Fin.ext h)
        exact Fin.ext (by omega)
    by_cases h0 : (0 : Fin 100) ∈ C
    · rw [card_erase_of_mem h0] at hpred
      omega
    · rw [erase_eq_of_notMem h0] at hpred
      omega
  omega

snip end

determine solution_value : ℕ := 8

problem usa2016_p1 : IsLeast {n | HasChain n} solution_value := by
  have hsv : solution_value = 8 := rfl
  refine ⟨hasChain_eight, ?_⟩
  rw [mem_lowerBounds]
  intro n hn
  by_contra hlt
  push Not at hlt
  rcases lt_or_ge n 7 with h | h
  · exact not_hasChain_of_le_six (by omega) hn
  · obtain rfl : n = 7 := by omega
    exact not_hasChain_seven hn

end Usa2016P1
