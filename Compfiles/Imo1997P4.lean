/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pjotr Buys
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Olympiad 1997, Problem 4

An $n \times n$ matrix whose entries come from the set
$S = \{1, 2, \ldots, 2n - 1\}$ is called a *silver matrix* if, for each
$i = 1, \ldots, n$, the $i$-th row and the $i$-th column together contain
all elements of $S$. Show that:

  (a) there is no silver matrix for $n = 1997$;

  (b) silver matrices exist for infinitely many values of $n$.
-/

namespace Imo1997P4

/-- An `n × n` matrix `M` is a *silver matrix* if its entries come from
`S = {1, …, 2n - 1}` and, for each `i`, the `i`-th row and the `i`-th column
together contain all of `S`. -/
def SilverMatrix (n : ℕ) (M : Fin n → Fin n → ℕ) : Prop :=
  (∀ i j, M i j ∈ Finset.Icc 1 (2 * n - 1)) ∧
  (∀ i, (Finset.univ.image (fun j ↦ M i j) ∪ Finset.univ.image (fun j ↦ M j i))
          = Finset.Icc 1 (2 * n - 1))

snip begin

open Finset

/-! ### Rows, columns and crosses -/

def row {n : ℕ} (i : Fin n) : Finset (Fin n × Fin n) := {i} ×ˢ univ

def col {n : ℕ} (i : Fin n) : Finset (Fin n × Fin n) := univ ×ˢ {i}

def cross {n : ℕ} (i : Fin n) : Finset (Fin n × Fin n) := row i ∪ col i

lemma card_row {n : ℕ} (i : Fin n) : (row i).card = n := by simp [row]

lemma card_col {n : ℕ} (i : Fin n) : (col i).card = n := by simp [col]

lemma row_mem {n : ℕ} (i j : Fin n) : (i, j) ∈ row i :=
  mk_mem_product (mem_singleton_self i) (mem_univ j)

lemma col_mem {n : ℕ} (i j : Fin n) : (i, j) ∈ col j :=
  mk_mem_product (mem_univ i) (mem_singleton_self j)

lemma cross_mem_left {n : ℕ} (i j : Fin n) : (i, j) ∈ cross i :=
  mem_union_left _ (row_mem _ _)

lemma row_union (n : ℕ) : (univ : Finset (Fin n)).biUnion row = univ :=
  eq_univ_iff_forall.2
    (fun (i, _) ↦ mem_biUnion.mpr ⟨i, mem_univ _, row_mem _ _⟩)

lemma col_union (n : ℕ) : (univ : Finset (Fin n)).biUnion col = univ :=
  eq_univ_iff_forall.2
    (fun (_, j) ↦ mem_biUnion.mpr ⟨j, mem_univ _, col_mem _ _⟩)

lemma row_disjoint (n : ℕ) : (Set.univ : Set (Fin n)).PairwiseDisjoint row :=
  fun _ _ _ _ h ↦ disjoint_product.2 (Or.inl (disjoint_singleton.2 h))

lemma col_disjoint (n : ℕ) : (Set.univ : Set (Fin n)).PairwiseDisjoint col :=
  fun _ _ _ _ h ↦ disjoint_product.2 (Or.inr (disjoint_singleton.2 h))

lemma row_inter_col {n : ℕ} (i : Fin n) : row i ∩ col i = {(i, i)} := by
  rw [row, col, product_inter_product]; simp

lemma card_cross {n : ℕ} (i : Fin n) : (cross i).card = 2 * n - 1 := by
  rw [cross, card_union, card_row, card_col, row_inter_col, card_singleton,
    Nat.two_mul]

lemma image_row {n : ℕ} (M : Fin n → Fin n → ℕ) (i : Fin n) :
    univ.image (fun j ↦ M i j) = (row i).image ↿M := by
  ext x; simp [row, Function.HasUncurry.uncurry]

lemma image_col {n : ℕ} (M : Fin n → Fin n → ℕ) (i : Fin n) :
    univ.image (fun j ↦ M j i) = (col i).image ↿M := by
  ext x; simp [col, Function.HasUncurry.uncurry]

lemma image_cross {n : ℕ} {M : Fin n → Fin n → ℕ} (h : SilverMatrix n M) (i : Fin n) :
    (cross i).image ↿M = Icc 1 (2 * n - 1) := by
  rw [cross, image_union, ← image_row, ← image_col]
  exact h.2 i

lemma silver_iff_cross {n : ℕ} (M : Fin n → Fin n → ℕ) :
    SilverMatrix n M ↔ ∀ i, (cross i).image ↿M = Icc 1 (2 * n - 1) := by
  refine ⟨image_cross, fun h ↦ ⟨fun i j ↦ ?_, fun i ↦ ?_⟩⟩ <;> rw [← h i]
  · exact mem_image.2 ⟨_, cross_mem_left i j, rfl⟩
  · rw [image_row, image_col, ← image_union, cross]

/-! ### Part (a): no silver matrix of odd size `n > 1` -/

lemma val_map_cross {n : ℕ} {M : Fin n → Fin n → ℕ} (h : SilverMatrix n M) (i : Fin n) :
    (cross i).val.map ↿M = Multiset.Icc 1 (2 * n - 1) := by
  rw [← image_val_of_injOn (injOn_of_card_image_eq (by
    simp [card_cross, image_cross h, Nat.card_Icc])), image_cross h i]; rfl

lemma multiset_row_col {n : ℕ} {M : Fin n → Fin n → ℕ} (h : SilverMatrix n M) (i : Fin n) :
    (row i).val.map ↿M + (col i).val.map ↿M
      = M i i ::ₘ Multiset.Icc 1 (2 * n - 1) := by
  rw [← val_map_cross h i, ← Multiset.map_add, ← Multiset.union_add_inter,
    ← union_val, ← inter_val, row_inter_col, singleton_val,
    Multiset.map_add, Multiset.map_singleton, ← Multiset.singleton_add, add_comm]; rfl

lemma sum_row_val {n : ℕ} : ∑ i : Fin n, (row i).val = univ.val := by
  rw [← row_union n, ← disjiUnion_eq_biUnion _ _ (by simpa using row_disjoint n)]; rfl

lemma sum_col_val {n : ℕ} : ∑ i : Fin n, (col i).val = univ.val := by
  rw [← col_union n, ← disjiUnion_eq_biUnion _ _ (by simpa using col_disjoint n)]; rfl

lemma sum_row_col_val {n : ℕ} (M : Fin n → Fin n → ℕ) :
    ∑ i, ((row i).val.map ↿M + (col i).val.map ↿M)
      = 2 • univ.val.map ↿M := by
  simp only [sum_add_distrib, ← Multiset.coe_mapAddMonoidHom, ← map_sum,
    sum_row_val, sum_col_val, two_nsmul]

lemma sum_row_col_val_silver {n : ℕ} {M : Fin n → Fin n → ℕ} (h : SilverMatrix n M) :
    ∑ i, ((row i).val.map ↿M + (col i).val.map ↿M)
      = univ.val.map (fun x ↦ M x x) + n • Multiset.Icc 1 (2 * n - 1) := by
  simp_rw [multiset_row_col h, ← Multiset.singleton_add, sum_add_distrib,
    sum_const, card_univ, Fintype.card_fin, ← Finset.sum_multiset_singleton,
    ← Multiset.coe_mapAddMonoidHom, map_sum]
  rfl

lemma exists_diag_count_zero {n : ℕ} (hn : 1 < n) (M : Fin n → Fin n → ℕ) :
    ∃ v ∈ Multiset.Icc 1 (2 * n - 1),
      (univ.val.map (fun x ↦ M x x)).count v = 0 := by
  set D := univ.val.map (fun x ↦ M x x) with hD
  have hcard : D.toFinset.card < (Icc 1 (2 * n - 1)).card := by
    have : D.toFinset.card ≤ n := by simpa [hD] using Multiset.toFinset_card_le D
    rw [Nat.card_Icc]
    omega
  obtain ⟨v, hv, hv'⟩ := exists_mem_notMem_of_card_lt_card hcard
  exact ⟨v, hv, by simpa using hv'⟩

lemma no_odd_SilverMatrix {n : ℕ} (hn : 1 < n) (hnodd : Odd n) :
    ¬ ∃ M : Fin n → Fin n → ℕ, SilverMatrix n M := by
  intro ⟨M, h⟩
  obtain ⟨x, hx₁, hx₂⟩ := exists_diag_count_zero hn M
  have heven : Even ((∑ i, ((row i).val.map ↿M + (col i).val.map ↿M)).count x) := by
    rw [sum_row_col_val M, Multiset.count_nsmul]
    exact even_two_mul _
  apply Nat.not_odd_iff_even.mpr heven
  rw [sum_row_col_val_silver h, Multiset.count_add, hx₂, zero_add,
    Multiset.count_nsmul, Multiset.count_eq_one_of_mem Multiset.nodup_Icc hx₁,
    mul_one]
  assumption

/-! ### Part (b): doubling a silver matrix -/

def blockMatrix {n : ℕ} (A B C D : Fin n → Fin n → ℕ) : Fin (n + n) → Fin (n + n) → ℕ :=
  fun a b ↦ Matrix.fromBlocks A B C D (finSumFinEquiv.symm a) (finSumFinEquiv.symm b)

lemma blockMatrix_row_left {n : ℕ} (A B C D : Fin n → Fin n → ℕ) (i : Fin n) :
    (row (finSumFinEquiv (.inl i))).image ↿(blockMatrix A B C D)
      = (row i).image ↿A ∪ (row i).image ↿B := by
  ext
  simp [← image_row, finSumFinEquiv.symm.exists_congr_left, blockMatrix]

lemma blockMatrix_row_right {n : ℕ} (A B C D : Fin n → Fin n → ℕ) (i : Fin n) :
    (row (finSumFinEquiv (.inr i))).image ↿(blockMatrix A B C D)
      = (row i).image ↿C ∪ (row i).image ↿D := by
  ext
  simp [← image_row, finSumFinEquiv.symm.exists_congr_left, blockMatrix,
     -finSumFinEquiv_apply_right]

lemma blockMatrix_col_left {n : ℕ} (A B C D : Fin n → Fin n → ℕ) (j : Fin n) :
    (col (finSumFinEquiv (.inl j))).image ↿(blockMatrix A B C D)
      = (col j).image ↿A ∪ (col j).image ↿C := by
  ext
  simp [← image_col, finSumFinEquiv.symm.exists_congr_left, blockMatrix]

lemma blockMatrix_col_right {n : ℕ} (A B C D : Fin n → Fin n → ℕ) (j : Fin n) :
    (col (finSumFinEquiv (.inr j))).image ↿(blockMatrix A B C D)
      = (col j).image ↿B ∪ (col j).image ↿D := by
  ext
  simp [← image_col, finSumFinEquiv.symm.exists_congr_left, blockMatrix,
    -finSumFinEquiv_apply_right]

lemma blockMatrix_cross_left {n : ℕ} (A B C D : Fin n → Fin n → ℕ) (i : Fin n) :
    (cross (finSumFinEquiv (.inl i))).image ↿(blockMatrix A B C D) =
    (cross i).image ↿A ∪ (row i).image ↿B ∪ (col i).image ↿C := by
  rw [cross, image_union, blockMatrix_row_left, blockMatrix_col_left, cross,
    image_union]
  ac_rfl

lemma blockMatrix_cross_right {n : ℕ} (A B C D : Fin n → Fin n → ℕ) (i : Fin n) :
    (cross (finSumFinEquiv (.inr i))).image ↿(blockMatrix A B C D) =
    (cross i).image ↿D ∪ (row i).image ↿C ∪ (col i).image ↿B := by
  rw [cross, image_union, blockMatrix_row_right, blockMatrix_col_right, cross,
    image_union]
  ac_rfl

def latinSquare {n : ℕ} (v : Fin n → ℕ) : Fin n → Fin n → ℕ := fun i j ↦ v (i - j)

lemma latinSquare_row {n : ℕ} (v : Fin n → ℕ) (i : Fin n) :
    (row i).image ↿(latinSquare v) = univ.image v := by
  haveI : NeZero n := ⟨i.pos.ne'⟩
  rw [← image_row, show (fun j ↦ latinSquare v i j) = v ∘ Equiv.subLeft i from rfl,
    ← Finset.image_image, Finset.image_univ_equiv]

lemma latinSquare_col {n : ℕ} (v : Fin n → ℕ) (j : Fin n) :
    (col j).image ↿(latinSquare v) = univ.image v := by
  haveI : NeZero n := ⟨j.pos.ne'⟩
  rw [← image_col, show (fun i ↦ latinSquare v i j) = v ∘ Equiv.subRight j from rfl,
    ← Finset.image_image, Finset.image_univ_equiv]

lemma Icc_union' {a b c : ℕ} (h : a ≤ b ∧ b ≤ c) : Icc a (b - 1) ∪ Icc b c = Icc a c := by
  ext _; simp only [mem_union, mem_Icc]; omega

lemma silver_double {n : ℕ} (hn : 1 ≤ n) (h : ∃ M, SilverMatrix n M) :
    ∃ M, SilverMatrix (n + n) M := by
  obtain ⟨M, hM⟩ := h
  refine ⟨blockMatrix M
    (latinSquare ((Icc (2 * n) (3 * n - 1)).orderEmbOfFin (by rw [Nat.card_Icc]; omega)))
    (latinSquare ((Icc (3 * n) (4 * n - 1)).orderEmbOfFin (by rw [Nat.card_Icc]; omega)))
    M, (silver_iff_cross _).2 fun a ↦ ?_⟩
  obtain ⟨_ | _, rfl⟩ := finSumFinEquiv.surjective a
  · rw [blockMatrix_cross_left, image_cross hM, latinSquare_row, latinSquare_col,
      image_orderEmbOfFin_univ, image_orderEmbOfFin_univ, Icc_union' (by omega),
      Icc_union' (by omega), (by ring : 2 * (n + n) = 4 * n)]
  · rw [blockMatrix_cross_right, image_cross hM, latinSquare_row, latinSquare_col,
      image_orderEmbOfFin_univ, image_orderEmbOfFin_univ, union_right_comm,
      Icc_union' (by omega), Icc_union' (by omega), (by ring : 2 * (n + n) = 4 * n)]

lemma silver_two_pow : ∀ k, ∃ M, SilverMatrix (2 ^ k) M
  | .zero   => ⟨1, by simp, by simp⟩
  | .succ _ => by
      rw [pow_succ, mul_two]
      exact silver_double Nat.one_le_two_pow (silver_two_pow _)

snip end

problem imo1997_p4 :
    (¬ ∃ M : Fin 1997 → Fin 1997 → ℕ, SilverMatrix 1997 M) ∧
    {n : ℕ | ∃ M : Fin n → Fin n → ℕ, SilverMatrix n M}.Infinite :=
  ⟨no_odd_SilverMatrix (by norm_num) ⟨998, by norm_num⟩,
  Set.infinite_of_injective_forall_mem (Nat.pow_right_injective le_rfl) silver_two_pow⟩

end Imo1997P4
