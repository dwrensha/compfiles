/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Data.Int.ConditionallyCompleteOrder
public import Mathlib.Data.Int.Interval
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Tactic.Ring
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics] }

/-!
# USA Mathematical Olympiad 2009, Problem 2

Let n be a positive integer. Determine the size of the largest subset of
{−n, −n+1, ..., n−1, n} which does not contain three elements a, b, c
(not necessarily distinct) satisfying a + b + c = 0.
-/

namespace Usa2009P2

/-- A set of integers is called *good* if it does not contain three elements
`a`, `b`, `c` (not necessarily distinct) satisfying `a + b + c = 0`. -/
abbrev IsGood (A : Finset ℤ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, a + b + c ≠ 0

determine answer (n : ℕ) : ℕ := if Even n then n else n + 1

snip begin

/-- The pairing map `x ↦ min x (c - x)` is injective on any set containing no two
elements summing to `c`: equality of the images forces `x = y` or `x + y = c`. -/
lemma injOn_min_sub {B : Finset ℤ} {c : ℤ} (hB : ∀ x ∈ B, ∀ y ∈ B, x + y ≠ c) :
    Set.InjOn (fun x ↦ min x (c - x)) B := by
  intro x hx y hy hxy
  dsimp only at hxy
  rcases min_choice x (c - x) with hx' | hx' <;>
    rcases min_choice y (c - y) with hy' | hy' <;>
    rw [hx', hy'] at hxy
  · exact hxy
  · exact absurd (by omega : x + y = c) (hB x hx y hy)
  · exact absurd (by omega : x + y = c) (hB x hx y hy)
  · omega

/-- Pairing counting lemma. If `B ⊆ [lo, hi]` contains no two elements (not necessarily
distinct) summing to `c = lo + hi`, then pairing `x` with `c - x` shows that `B` has at
most as many elements as the interval `[lo, (c-1)/2]`. -/
lemma card_le_of_pair {B : Finset ℤ} {lo hi c : ℤ} (hsub : B ⊆ Finset.Icc lo hi)
    (hc : c = lo + hi) (hB : ∀ x ∈ B, ∀ y ∈ B, x + y ≠ c) :
    B.card ≤ ((c - 1) / 2 + 1 - lo).toNat := by
  have hmem : ∀ x ∈ B, min x (c - x) ∈ Finset.Icc lo ((c - 1) / 2) := by
    intro x hx
    have hlo : lo ≤ x := (Finset.mem_Icc.mp (hsub hx)).1
    have hhi : x ≤ hi := (Finset.mem_Icc.mp (hsub hx)).2
    have hxx : x + x ≠ c := hB x hx x hx
    rw [Finset.mem_Icc]
    refine ⟨le_min_iff.mpr ⟨hlo, by omega⟩, ?_⟩
    by_contra hcon
    push Not at hcon
    have h1 : (c - 1) / 2 < x := lt_of_lt_of_le hcon (min_le_left _ _)
    have h2 : (c - 1) / 2 < c - x := lt_of_lt_of_le hcon (min_le_right _ _)
    omega
  calc B.card ≤ (Finset.Icc lo ((c - 1) / 2)).card :=
        Finset.card_le_card_of_injOn _ hmem (injOn_min_sub hB)
    _ = ((c - 1) / 2 + 1 - lo).toNat := Int.card_Icc _ _

/-- Case (ii) of the induction step: if both `2m` and `-(2m)` lie in `A` (with `m ≥ 1`),
then `A` has at most `2m` elements. -/
lemma card_le_case2 {m : ℕ} (hm : 1 ≤ m) {A : Finset ℤ}
    (hsub : A ⊆ Finset.Icc (-(2 * (m : ℤ))) (2 * (m : ℤ))) (hgood : IsGood A)
    (hN : (2 * (m : ℤ)) ∈ A) (hnegN : -(2 * (m : ℤ)) ∈ A) :
    A.card ≤ 2 * m := by
  have h0 : (0 : ℤ) ∉ A := fun h0 ↦ hgood _ hN _ hnegN _ h0 (by ring)
  -- The negative part of `A`, mapped to the positive interval `[1, 2m-1]`.
  set Bm := (A ∩ Finset.Icc (-(2 * (m : ℤ)) + 1) (-1)).image (fun x ↦ -x) with hBm
  -- Positive part: at most one element from each pair `{i, 2m-i}`.
  have hpos : (A ∩ Finset.Icc 1 (2 * (m : ℤ) - 1)).card ≤ m - 1 := by
    have h := card_le_of_pair (lo := 1) (hi := 2 * (m : ℤ) - 1) (c := 2 * (m : ℤ))
      Finset.inter_subset_right (by ring)
      (fun x hx y hy hxy ↦ hgood _ hnegN _ (Finset.mem_inter.mp hx).1 _
        (Finset.mem_inter.mp hy).1 (by omega))
    have hnum : ((2 * (m : ℤ) - 1) / 2 + 1 - 1).toNat = m - 1 := by omega
    rwa [hnum] at h
  -- Negative part: same bound, after negation.
  have hnegsub : Bm ⊆ Finset.Icc 1 (2 * (m : ℤ) - 1) := by
    intro x hx
    rw [hBm, Finset.mem_image] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hy' := Finset.mem_Icc.mp (Finset.mem_inter.mp hy).2
    rw [Finset.mem_Icc]
    omega
  have hneggood : ∀ x ∈ Bm, ∀ y ∈ Bm, x + y ≠ 2 * (m : ℤ) := by
    intro x hx y hy hxy
    rw [hBm, Finset.mem_image] at hx hy
    obtain ⟨x', hx', rfl⟩ := hx
    obtain ⟨y', hy', rfl⟩ := hy
    exact hgood _ hN _ (Finset.mem_inter.mp hx').1 _ (Finset.mem_inter.mp hy').1 (by omega)
  have hneg : (A ∩ Finset.Icc (-(2 * (m : ℤ)) + 1) (-1)).card ≤ m - 1 := by
    have h1 : (A ∩ Finset.Icc (-(2 * (m : ℤ)) + 1) (-1)).card = Bm.card := by
      rw [hBm]
      exact (Finset.card_image_of_injective _ neg_injective).symm
    rw [h1]
    have h := card_le_of_pair (lo := 1) (hi := 2 * (m : ℤ) - 1) (c := 2 * (m : ℤ))
      hnegsub (by ring) hneggood
    have hnum : ((2 * (m : ℤ) - 1) / 2 + 1 - 1).toNat = m - 1 := by omega
    rwa [hnum] at h
  -- Now `A ⊆ {-2m, 2m} ∪ (positive part) ∪ (negative part)`.
  have hsplit : A ⊆ {-(2 * (m : ℤ)), 2 * (m : ℤ)} ∪
      ((A ∩ Finset.Icc 1 (2 * (m : ℤ) - 1)) ∪
        (A ∩ Finset.Icc (-(2 * (m : ℤ)) + 1) (-1))) := by
    intro x hx
    have hrange := Finset.mem_Icc.mp (hsub hx)
    rw [Finset.mem_union, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    by_cases hxp : x ∈ A ∩ Finset.Icc 1 (2 * (m : ℤ) - 1)
    · exact Or.inr (Or.inl hxp)
    · by_cases hxn : x ∈ A ∩ Finset.Icc (-(2 * (m : ℤ)) + 1) (-1)
      · exact Or.inr (Or.inr hxn)
      · left
        have hx0 : x ≠ 0 := fun h ↦ h0 (h ▸ hx)
        have hxa : x ∉ Finset.Icc 1 (2 * (m : ℤ) - 1) :=
          fun h ↦ hxp (Finset.mem_inter.mpr ⟨hx, h⟩)
        have hxb : x ∉ Finset.Icc (-(2 * (m : ℤ)) + 1) (-1) :=
          fun h ↦ hxn (Finset.mem_inter.mpr ⟨hx, h⟩)
        rw [Finset.mem_Icc] at hxa hxb
        omega
  have h2 : ({-(2 * (m : ℤ)), 2 * (m : ℤ)} : Finset ℤ).card ≤ 2 :=
    le_trans (Finset.card_insert_le _ _) (by simp)
  have h3 : ((A ∩ Finset.Icc 1 (2 * (m : ℤ) - 1)) ∪
        (A ∩ Finset.Icc (-(2 * (m : ℤ)) + 1) (-1))).card ≤ (m - 1) + (m - 1) :=
    le_trans (Finset.card_union_le _ _) (by omega)
  refine le_trans (Finset.card_le_card hsplit) ?_
  refine le_trans (Finset.card_union_le _ _) ?_
  omega

/-- Case (iii) of the induction step: if `2m`, `2m-1` and `-(2m-1)` lie in `A` but
`-(2m)` does not (with `m ≥ 1`), then `A` has at most `2m` elements. -/
lemma card_le_case3 {m : ℕ} (hm : 1 ≤ m) {A : Finset ℤ}
    (hsub : A ⊆ Finset.Icc (-(2 * (m : ℤ))) (2 * (m : ℤ))) (hgood : IsGood A)
    (hN : (2 * (m : ℤ)) ∈ A) (hN1 : (2 * (m : ℤ)) - 1 ∈ A)
    (hnegN1 : -((2 * (m : ℤ)) - 1) ∈ A) (hnegN : -(2 * (m : ℤ)) ∉ A) :
    A.card ≤ 2 * m := by
  by_cases hm1 : m = 1
  · -- If `m = 1` then `-1 = -(2m-1) ∈ A` and `2m + (-1) + (-1) = 0`: contradiction.
    subst hm1
    exfalso
    have h2 : (2 : ℤ) ∈ A := by norm_num at hN ⊢; exact hN
    have h1 : (-1 : ℤ) ∈ A := by norm_num at hnegN1 ⊢; exact hnegN1
    exact hgood 2 h2 (-1) h1 (-1) h1 (by norm_num)
  · have hm2 : 2 ≤ m := by omega
    have h0 : (0 : ℤ) ∉ A := fun h0 ↦ hgood _ hN1 _ hnegN1 _ h0 (by ring)
    have hneg1 : (-1 : ℤ) ∉ A := fun h ↦ hgood _ hN _ hnegN1 _ h (by ring)
    -- Positive part: at most one element from each pair `{i, 2m-1-i}` of `[1, 2m-2]`.
    have hpos : (A ∩ Finset.Icc 1 (2 * (m : ℤ) - 2)).card ≤ m - 1 := by
      have h := card_le_of_pair (lo := 1) (hi := 2 * (m : ℤ) - 2) (c := 2 * (m : ℤ) - 1)
        Finset.inter_subset_right (by ring)
        (fun x hx y hy hxy ↦ hgood _ hnegN1 _ (Finset.mem_inter.mp hx).1 _
          (Finset.mem_inter.mp hy).1 (by omega))
      have hnum : ((2 * (m : ℤ) - 1 - 1) / 2 + 1 - 1).toNat = m - 1 := by omega
      rwa [hnum] at h
    -- Negative part: the images under negation land in `[2, 2m-2]`, with pairs summing
    -- to `2m`.
    set Bm := (A ∩ Finset.Icc (-(2 * (m : ℤ)) + 2) (-2)).image (fun x ↦ -x) with hBm
    have hnegsub : Bm ⊆ Finset.Icc 2 (2 * (m : ℤ) - 2) := by
      intro x hx
      rw [hBm, Finset.mem_image] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      have hy' := Finset.mem_Icc.mp (Finset.mem_inter.mp hy).2
      rw [Finset.mem_Icc]
      omega
    have hneggood : ∀ x ∈ Bm, ∀ y ∈ Bm, x + y ≠ 2 * (m : ℤ) := by
      intro x hx y hy hxy
      rw [hBm, Finset.mem_image] at hx hy
      obtain ⟨x', hx', rfl⟩ := hx
      obtain ⟨y', hy', rfl⟩ := hy
      exact hgood _ hN _ (Finset.mem_inter.mp hx').1 _ (Finset.mem_inter.mp hy').1
        (by omega)
    have hneg : (A ∩ Finset.Icc (-(2 * (m : ℤ)) + 2) (-2)).card ≤ m - 2 := by
      have h1 : (A ∩ Finset.Icc (-(2 * (m : ℤ)) + 2) (-2)).card = Bm.card := by
        rw [hBm]
        exact (Finset.card_image_of_injective _ neg_injective).symm
      rw [h1]
      have h := card_le_of_pair (lo := 2) (hi := 2 * (m : ℤ) - 2) (c := 2 * (m : ℤ))
        hnegsub (by ring) hneggood
      have hnum : ((2 * (m : ℤ) - 1) / 2 + 1 - 2).toNat = m - 2 := by omega
      rwa [hnum] at h
    -- Now `A ⊆ {2m, 2m-1, -(2m-1)} ∪ (positive part) ∪ (negative part)`.
    have hsplit : A ⊆ {2 * (m : ℤ), 2 * (m : ℤ) - 1, -((2 * (m : ℤ)) - 1)} ∪
        ((A ∩ Finset.Icc 1 (2 * (m : ℤ) - 2)) ∪
          (A ∩ Finset.Icc (-(2 * (m : ℤ)) + 2) (-2))) := by
      intro x hx
      have hrange := Finset.mem_Icc.mp (hsub hx)
      have hx0 : x ≠ 0 := fun h ↦ h0 (h ▸ hx)
      have hxneg1 : x ≠ -1 := fun h ↦ hneg1 (h ▸ hx)
      have hxnegN : x ≠ -(2 * (m : ℤ)) := fun h ↦ hnegN (h ▸ hx)
      rw [Finset.mem_union, Finset.mem_union]
      by_cases hxp : x ∈ A ∩ Finset.Icc 1 (2 * (m : ℤ) - 2)
      · exact Or.inr (Or.inl hxp)
      · by_cases hxn : x ∈ A ∩ Finset.Icc (-(2 * (m : ℤ)) + 2) (-2)
        · exact Or.inr (Or.inr hxn)
        · left
          have hxa : x ∉ Finset.Icc 1 (2 * (m : ℤ) - 2) :=
            fun h ↦ hxp (Finset.mem_inter.mpr ⟨hx, h⟩)
          have hxb : x ∉ Finset.Icc (-(2 * (m : ℤ)) + 2) (-2) :=
            fun h ↦ hxn (Finset.mem_inter.mpr ⟨hx, h⟩)
          rw [Finset.mem_Icc] at hxa hxb
          simp only [Finset.mem_insert, Finset.mem_singleton]
          omega
    have htri : ({2 * (m : ℤ), 2 * (m : ℤ) - 1, -((2 * (m : ℤ)) - 1)} : Finset ℤ).card ≤ 3 := by
      refine le_trans (Finset.card_insert_le _ _) ?_
      refine le_trans (Nat.add_le_add_right (Finset.card_insert_le _ _) 1) ?_
      simp
    have h3 : ((A ∩ Finset.Icc 1 (2 * (m : ℤ) - 2)) ∪
          (A ∩ Finset.Icc (-(2 * (m : ℤ)) + 2) (-2))).card ≤ (m - 1) + (m - 2) :=
      le_trans (Finset.card_union_le _ _) (by omega)
    refine le_trans (Finset.card_le_card hsplit) ?_
    refine le_trans (Finset.card_union_le _ _) ?_
    omega

/-- The upper bound for even `n`: any good subset of `[-2m, 2m]` has at most `2m`
elements, by strong induction on `m`. -/
lemma card_le_even (m : ℕ) (A : Finset ℤ) :
    A ⊆ Finset.Icc (-(2 * (m : ℤ))) (2 * (m : ℤ)) → IsGood A → A.card ≤ 2 * m := by
  induction m using Nat.strong_induction_on generalizing A with
  | _ m ih =>
    intro hsub hgood
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · -- `m = 0`: `A ⊆ {0}`, but `0 ∉ A` since `0 + 0 + 0 = 0`.
      have h0 : (0 : ℤ) ∉ A := fun h0 ↦ hgood 0 h0 0 h0 0 h0 (by norm_num)
      rcases Finset.eq_empty_or_nonempty A with rfl | hne
      · simp
      · obtain ⟨x, hx⟩ := hne
        have hx0 : x = 0 := by
          have h := hsub hx
          simp only [Nat.cast_zero, mul_zero, neg_zero] at h
          rw [Finset.mem_Icc] at h
          exact le_antisymm h.2 h.1
        exact absurd (hx0 ▸ hx) h0
    · -- Common argument when at most two of `{2m, -(2m), 2m-1, -(2m-1)}` lie in `A`:
      -- remove them and apply the induction hypothesis for `m - 1`.
      have endpoint : ∀ S : Finset ℤ, S.card ≤ 2 →
          (∀ x ∈ A, x ∉ Finset.Icc (-(2 * (m : ℤ) - 2)) (2 * (m : ℤ) - 2) → x ∈ S) →
          A.card ≤ 2 * m := by
        intro S hS hmem
        have hAu : A ⊆ (A ∩ Finset.Icc (-(2 * (m : ℤ) - 2)) (2 * (m : ℤ) - 2)) ∪ S := by
          intro x hx
          rw [Finset.mem_union]
          by_cases hx2 : x ∈ Finset.Icc (-(2 * (m : ℤ) - 2)) (2 * (m : ℤ) - 2)
          · exact Or.inl (Finset.mem_inter.mpr ⟨hx, hx2⟩)
          · exact Or.inr (hmem x hx hx2)
        have hcard : (A ∩ Finset.Icc (-(2 * (m : ℤ) - 2)) (2 * (m : ℤ) - 2)).card ≤
            2 * (m - 1) := by
          apply ih (m - 1) (by omega)
          · intro x hx
            have hx' := Finset.mem_Icc.mp (Finset.mem_inter.mp hx).2
            have hm1 : ((m - 1 : ℕ) : ℤ) = (m : ℤ) - 1 := by omega
            rw [Finset.mem_Icc, hm1]
            omega
          · intro a ha b hb c hc
            exact hgood a (Finset.mem_inter.mp ha).1 b (Finset.mem_inter.mp hb).1
              c (Finset.mem_inter.mp hc).1
        calc A.card ≤ ((A ∩ Finset.Icc (-(2 * (m : ℤ) - 2)) (2 * (m : ℤ) - 2)) ∪ S).card :=
              Finset.card_le_card hAu
          _ ≤ (A ∩ Finset.Icc (-(2 * (m : ℤ) - 2)) (2 * (m : ℤ) - 2)).card + S.card :=
              Finset.card_union_le _ _
          _ ≤ 2 * m := by omega
      by_cases hN : (2 * (m : ℤ)) ∈ A
      · by_cases hnegN : -(2 * (m : ℤ)) ∈ A
        · exact card_le_case2 hm hsub hgood hN hnegN
        · by_cases hN1 : (2 * (m : ℤ)) - 1 ∈ A
          · by_cases hnegN1 : -((2 * (m : ℤ)) - 1) ∈ A
            · exact card_le_case3 hm hsub hgood hN hN1 hnegN1 hnegN
            · refine endpoint {2 * (m : ℤ), 2 * (m : ℤ) - 1}
                (le_trans (Finset.card_insert_le _ _) (by simp)) ?_
              intro x hx hxout
              have hrange := Finset.mem_Icc.mp (hsub hx)
              have hx1 : x ≠ -(2 * (m : ℤ)) := fun h ↦ hnegN (h ▸ hx)
              have hx2 : x ≠ -((2 * (m : ℤ)) - 1) := fun h ↦ hnegN1 (h ▸ hx)
              rw [Finset.mem_Icc] at hxout
              simp only [Finset.mem_insert, Finset.mem_singleton]
              omega
          · refine endpoint {2 * (m : ℤ), -((2 * (m : ℤ)) - 1)}
              (le_trans (Finset.card_insert_le _ _) (by simp)) ?_
            intro x hx hxout
            have hrange := Finset.mem_Icc.mp (hsub hx)
            have hx1 : x ≠ -(2 * (m : ℤ)) := fun h ↦ hnegN (h ▸ hx)
            have hx2 : x ≠ (2 * (m : ℤ)) - 1 := fun h ↦ hN1 (h ▸ hx)
            rw [Finset.mem_Icc] at hxout
            simp only [Finset.mem_insert, Finset.mem_singleton]
            omega
      · by_cases hnegN : -(2 * (m : ℤ)) ∈ A
        · by_cases hN1 : (2 * (m : ℤ)) - 1 ∈ A
          · by_cases hnegN1 : -((2 * (m : ℤ)) - 1) ∈ A
            · -- Symmetric case (iii): apply case 3 to `-A`.
              have hsub' : A.image (fun x ↦ -x) ⊆ Finset.Icc (-(2 * (m : ℤ))) (2 * (m : ℤ)) := by
                intro x hx
                rw [Finset.mem_image] at hx
                obtain ⟨y, hy, rfl⟩ := hx
                have hyy := Finset.mem_Icc.mp (hsub hy)
                rw [Finset.mem_Icc]
                omega
              have hgood' : IsGood (A.image (fun x ↦ -x)) := by
                intro a ha b hb c hc
                rw [Finset.mem_image] at ha hb hc
                obtain ⟨a', ha', rfl⟩ := ha
                obtain ⟨b', hb', rfl⟩ := hb
                obtain ⟨c', hc', rfl⟩ := hc
                have h := hgood a' ha' b' hb' c' hc'
                omega
              have hN' : (2 * (m : ℤ)) ∈ A.image (fun x ↦ -x) :=
                Finset.mem_image.mpr ⟨_, hnegN, by simp⟩
              have hN1' : (2 * (m : ℤ)) - 1 ∈ A.image (fun x ↦ -x) :=
                Finset.mem_image.mpr ⟨_, hnegN1, by simp⟩
              have hnegN1' : -((2 * (m : ℤ)) - 1) ∈ A.image (fun x ↦ -x) :=
                Finset.mem_image.mpr ⟨_, hN1, by simp⟩
              have hnegN' : -(2 * (m : ℤ)) ∉ A.image (fun x ↦ -x) := by
                intro hcontra
                rw [Finset.mem_image] at hcontra
                obtain ⟨y, hy, hyy⟩ := hcontra
                have hyeq : y = 2 * (m : ℤ) := neg_inj.mp hyy
                exact hN (hyeq ▸ hy)
              have hle := card_le_case3 hm hsub' hgood' hN' hN1' hnegN1' hnegN'
              have hcard : (A.image (fun x ↦ -x)).card = A.card :=
                Finset.card_image_of_injective _ neg_injective
              omega
            · refine endpoint {-(2 * (m : ℤ)), 2 * (m : ℤ) - 1}
                (le_trans (Finset.card_insert_le _ _) (by simp)) ?_
              intro x hx hxout
              have hrange := Finset.mem_Icc.mp (hsub hx)
              have hx1 : x ≠ 2 * (m : ℤ) := fun h ↦ hN (h ▸ hx)
              have hx2 : x ≠ -((2 * (m : ℤ)) - 1) := fun h ↦ hnegN1 (h ▸ hx)
              rw [Finset.mem_Icc] at hxout
              simp only [Finset.mem_insert, Finset.mem_singleton]
              omega
          · refine endpoint {-(2 * (m : ℤ)), -((2 * (m : ℤ)) - 1)}
              (le_trans (Finset.card_insert_le _ _) (by simp)) ?_
            intro x hx hxout
            have hrange := Finset.mem_Icc.mp (hsub hx)
            have hx1 : x ≠ 2 * (m : ℤ) := fun h ↦ hN (h ▸ hx)
            have hx2 : x ≠ (2 * (m : ℤ)) - 1 := fun h ↦ hN1 (h ▸ hx)
            rw [Finset.mem_Icc] at hxout
            simp only [Finset.mem_insert, Finset.mem_singleton]
            omega
        · refine endpoint {2 * (m : ℤ) - 1, -((2 * (m : ℤ)) - 1)}
            (le_trans (Finset.card_insert_le _ _) (by simp)) ?_
          intro x hx hxout
          have hrange := Finset.mem_Icc.mp (hsub hx)
          have hx1 : x ≠ 2 * (m : ℤ) := fun h ↦ hN (h ▸ hx)
          have hx2 : x ≠ -(2 * (m : ℤ)) := fun h ↦ hnegN (h ▸ hx)
          rw [Finset.mem_Icc] at hxout
          simp only [Finset.mem_insert, Finset.mem_singleton]
          omega

snip end

problem usa2009_p2 (n : ℕ) (hn : 0 < n) :
    IsGreatest
      {k : ℕ | ∃ A : Finset ℤ,
        A ⊆ Finset.Icc (-(n : ℤ)) (n : ℤ) ∧ IsGood A ∧ A.card = k}
      (answer n) := by
  constructor
  · -- Construction: all elements with absolute value larger than `n / 2`.
    refine ⟨Finset.Icc (-(n : ℤ)) (-((n / 2 + 1 : ℕ) : ℤ)) ∪
      Finset.Icc ((n / 2 + 1 : ℕ) : ℤ) (n : ℤ), ?_, ?_, ?_⟩
    · intro x hx
      rw [Finset.mem_union] at hx
      rcases hx with hx | hx <;> rw [Finset.mem_Icc] at hx ⊢ <;> omega
    · intro a ha b hb c hc hsum
      have hK : 2 * (((n / 2 + 1 : ℕ)) : ℤ) ≥ (n : ℤ) + 1 := by omega
      rw [Finset.mem_union] at ha hb hc
      rcases ha with ha | ha <;> rcases hb with hb | hb <;> rcases hc with hc | hc <;>
        · rw [Finset.mem_Icc] at ha hb hc
          omega
    · have hdisj : Disjoint (Finset.Icc (-(n : ℤ)) (-((n / 2 + 1 : ℕ) : ℤ)))
          (Finset.Icc ((n / 2 + 1 : ℕ) : ℤ) (n : ℤ)) := by
        rw [Finset.disjoint_left]
        intro x hx1 hx2
        rw [Finset.mem_Icc] at hx1 hx2
        omega
      rw [Finset.card_union_of_disjoint hdisj, Int.card_Icc, Int.card_Icc]
      simp only [answer]
      by_cases hev : Even n
      · rw [ite_eq_left hev]
        obtain ⟨t, ht⟩ := hev
        omega
      · rw [ite_eq_right hev]
        have hoddn : n % 2 = 1 := by
          rcases Nat.even_or_odd n with h | h
          · exact absurd h hev
          · exact Nat.odd_iff.mp h
        omega
  · -- Upper bound: the odd case reduces to the even case applied to `[-(n+1), n+1]`.
    intro k hk
    obtain ⟨A, hsub, hgood, rfl⟩ := hk
    rcases Nat.even_or_odd n with hev | hodd
    · obtain ⟨m, rfl⟩ := hev
      have hn2 : ((m + m : ℕ) : ℤ) = 2 * (m : ℤ) := by push_cast; ring
      rw [hn2] at hsub
      have hle := card_le_even m A hsub hgood
      simp only [answer]
      rw [ite_eq_left (show Even (m + m) from ⟨m, rfl⟩)]
      omega
    · obtain ⟨m, hm⟩ := hodd
      subst hm
      have hsub' : A ⊆ Finset.Icc (-(2 * ((m + 1 : ℕ) : ℤ))) (2 * ((m + 1 : ℕ) : ℤ)) := by
        intro x hx
        have hxx := Finset.mem_Icc.mp (hsub hx)
        rw [Finset.mem_Icc]
        have hcast : ((m + 1 : ℕ) : ℤ) = (m : ℤ) + 1 := by push_cast; ring
        rw [hcast]
        omega
      have hle := card_le_even (m + 1) A hsub' hgood
      simp only [answer]
      rw [ite_eq_right (show ¬Even (2 * m + 1) by
        rw [Nat.not_even_iff_odd]; exact ⟨m, rfl⟩)]
      omega

end Usa2009P2
