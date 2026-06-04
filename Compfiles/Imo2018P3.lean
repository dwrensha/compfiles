/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Olympiad 2018, Problem 3

An anti-Pascal triangle is an equilateral triangular array of numbers such that,
except for the numbers in the bottom row, each number is the absolute value
of the difference of the two numbers immediately below it. For example,
the following array is an anti-Pascal triangle with four rows
which contains every integer from 1 to 10:

                  4
                2   6
              5   7   1
            8   3  10   9

Does there exist an anti-Pascal triangle with 2018 rows which contains every
integer from 1 to 1 + 2 + ... + 2018?
-/

namespace Imo2018P3

structure Coords where
(row : ℕ) (col : ℕ)
deriving DecidableEq

def left_child (c : Coords) : Coords :=
 ⟨c.row.succ, c.col⟩

def right_child (c : Coords) : Coords :=
  ⟨c.row.succ, c.col.succ⟩

/--
antipascal triangle with n rows
-/
structure antipascal_triangle (n : ℕ) where
(f : Coords → ℕ)
(antipascal : ∀ x : Coords, x.row + 1 < n ∧ x.col ≤ x.row →
  f x + f (left_child x) = f (right_child x) ∨
  f x + f (right_child x) = f (left_child x))

def exists_desired_triangle : Prop :=
   ∃ t : antipascal_triangle 2018,
     ∀ n, 1 ≤ n → n ≤ ∑ i ∈ Finset.range 2018, (i + 1) →
         ∃ r, r < 2018 ∧ ∃ c, c ≤ r ∧ t.f ⟨r,c⟩ = n

snip begin


/-- Number of rows. -/
private def NR : ℕ := 2018

/-- The total `1 + 2 + ⋯ + 2018`. -/
private def TN : ℕ := ∑ i ∈ Finset.range NR, (i + 1)

private lemma NR_val : NR = 2018 := rfl

private lemma TN_def : (∑ i ∈ Finset.range NR, (i + 1)) = TN := rfl

/-- The set of cells of an `NR`-row triangle: row `< NR`, column `≤ row`. -/
private def tri : Finset Coords :=
  (Finset.range NR).biUnion (fun r => (Finset.range (r + 1)).image (fun c => ⟨r, c⟩))

-- Keep `tri` from being unfolded (and `Finset.range 2018` evaluated) during unification.
attribute [local irreducible] tri

private lemma mem_tri {x : Coords} : x ∈ tri ↔ x.row < NR ∧ x.col ≤ x.row := by
  simp only [tri, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image]
  constructor
  · rintro ⟨r, hr, c, hc, rfl⟩
    exact ⟨hr, Nat.lt_succ_iff.mp hc⟩
  · rintro ⟨hr, hc⟩
    exact ⟨x.row, hr, x.col, Nat.lt_succ_iff.mpr hc, rfl⟩

private lemma card_tri : tri.card = TN := by
  rw [tri, TN, Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro r _
    rw [Finset.card_image_of_injective _ (fun a b h => by simpa using h), Finset.card_range]
  · intro r1 _ r2 _ hne
    simp only [Finset.disjoint_left, Finset.mem_image, Finset.mem_range]
    rintro x ⟨c1, _, rfl⟩ ⟨c2, _, h⟩
    rw [Coords.mk.injEq] at h
    exact hne h.1.symm

/-- The sum of `n` distinct positive integers is at least `1 + 2 + ⋯ + n`. -/
private lemma min_sum : ∀ (V : Finset ℕ), (∀ x ∈ V, 1 ≤ x) →
    ∑ i ∈ Finset.range V.card, (i + 1) ≤ ∑ x ∈ V, x := by
  intro V
  induction V using Finset.strongInduction with
  | _ V ih =>
    intro hpos
    rcases V.eq_empty_or_nonempty with h | h
    · subst h; simp
    · set M := V.max' h with hMdef
      have hMmem : M ∈ V := V.max'_mem h
      have hcardM : V.card ≤ M := by
        calc V.card ≤ (Finset.Icc 1 M).card :=
              Finset.card_le_card (fun x hx => Finset.mem_Icc.mpr ⟨hpos x hx, V.le_max' x hx⟩)
          _ = M := by rw [Nat.card_Icc, Nat.add_sub_cancel]
      have hcardpos : 1 ≤ V.card := Finset.card_pos.mpr h
      have herase : (V.erase M).card = V.card - 1 := Finset.card_erase_of_mem hMmem
      have key := ih (V.erase M) (Finset.erase_ssubset hMmem)
                    (fun x hx => hpos x (Finset.mem_of_mem_erase hx))
      have hsplit : ∑ x ∈ V.erase M, x + M = ∑ x ∈ V, x :=
        Finset.sum_erase_add V _ hMmem
      have hrange : ∑ i ∈ Finset.range V.card, (i + 1)
          = ∑ i ∈ Finset.range (V.card - 1), (i + 1) + V.card := by
        conv_lhs => rw [show V.card = (V.card - 1) + 1 by omega, Finset.sum_range_succ]
        omega
      rw [herase] at key
      omega

/-- `n` distinct positive integers with sum at most `1 + 2 + ⋯ + n` are exactly `{1, …, n}`. -/
private lemma min_sum_eq : ∀ (V : Finset ℕ), (∀ x ∈ V, 1 ≤ x) →
    ∑ x ∈ V, x ≤ ∑ i ∈ Finset.range V.card, (i + 1) →
    V = Finset.Icc 1 V.card := by
  intro V
  induction V using Finset.strongInduction with
  | _ V ih =>
    intro hpos hsum
    rcases V.eq_empty_or_nonempty with h | h
    · subst h; simp
    · set M := V.max' h with hMdef
      have hMmem : M ∈ V := V.max'_mem h
      have hcardM : V.card ≤ M := by
        calc V.card ≤ (Finset.Icc 1 M).card :=
              Finset.card_le_card (fun x hx => Finset.mem_Icc.mpr ⟨hpos x hx, V.le_max' x hx⟩)
          _ = M := by rw [Nat.card_Icc, Nat.add_sub_cancel]
      have hcardpos : 1 ≤ V.card := Finset.card_pos.mpr h
      have herase : (V.erase M).card = V.card - 1 := Finset.card_erase_of_mem hMmem
      have hkey := min_sum (V.erase M) (fun x hx => hpos x (Finset.mem_of_mem_erase hx))
      rw [herase] at hkey
      have hsplit : ∑ x ∈ V.erase M, x + M = ∑ x ∈ V, x :=
        Finset.sum_erase_add V _ hMmem
      have hrange : ∑ i ∈ Finset.range V.card, (i + 1)
          = ∑ i ∈ Finset.range (V.card - 1), (i + 1) + V.card := by
        conv_lhs => rw [show V.card = (V.card - 1) + 1 by omega, Finset.sum_range_succ]
        omega
      have hMeq : M = V.card := by omega
      have herase_le : ∑ x ∈ V.erase M, x ≤ ∑ i ∈ Finset.range (V.card - 1), (i + 1) := by omega
      have hV'eq := ih (V.erase M) (Finset.erase_ssubset hMmem)
                      (fun x hx => hpos x (Finset.mem_of_mem_erase hx))
                      (by rw [herase]; exact herase_le)
      rw [herase] at hV'eq
      ext y
      rw [Finset.mem_Icc]
      constructor
      · intro hy
        exact ⟨hpos y hy, by rw [← hMeq]; exact V.le_max' y hy⟩
      · rintro ⟨hy1, hy2⟩
        by_cases hyM : y = M
        · rw [hyM]; exact hMmem
        · have hye : y ∈ V.erase M := by
            rw [hV'eq, Finset.mem_Icc]
            rw [hMeq] at hyM
            omega
          exact Finset.mem_of_mem_erase hye

private lemma two_mul_sum (n : ℕ) : 2 * (∑ i ∈ Finset.range n, (i + 1)) = n * (n + 1) := by
  induction n with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, Nat.mul_add, ih]; ring

/-- The sum of `n` distinct integers each `> m` is at least `n·m + (1 + ⋯ + n)`. -/
private lemma min_sum_ge (V : Finset ℕ) (m : ℕ) (hpos : ∀ x ∈ V, m < x) :
    V.card * m + ∑ i ∈ Finset.range V.card, (i + 1) ≤ ∑ x ∈ V, x := by
  classical
  have hinj : Set.InjOn (· - m) ↑V := by
    intro a ha b hb hab
    simp only [] at hab
    have h1 := hpos a ha; have h2 := hpos b hb; omega
  have hWcard : (V.image (· - m)).card = V.card := Finset.card_image_of_injOn hinj
  have hWpos : ∀ x ∈ V.image (· - m), 1 ≤ x := by
    intro x hx; rw [Finset.mem_image] at hx; obtain ⟨a, ha, rfl⟩ := hx
    have := hpos a ha; omega
  have hmin := min_sum (V.image (· - m)) hWpos
  rw [hWcard, Finset.sum_image hinj] at hmin
  have hsplit : ∑ x ∈ V, x = (∑ a ∈ V, (a - m)) + V.card * m := by
    have hc : ∑ x ∈ V, x = ∑ a ∈ V, ((a - m) + m) := by
      apply Finset.sum_congr rfl; intro a ha; have := hpos a ha; omega
    rw [hc, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul]
  omega

section
variable (t : antipascal_triangle NR)
variable (hsurj : ∀ v, 1 ≤ v → v ≤ TN →
                    ∃ r, r < NR ∧ ∃ c, c ≤ r ∧ t.f ⟨r, c⟩ = v)

include hsurj in
/-- Every cell value lies in `[1, TN]` and `t.f` is injective on the triangle. -/
private lemma bijection :
    (∀ x ∈ tri, 1 ≤ t.f x ∧ t.f x ≤ TN) ∧ Set.InjOn t.f ↑tri := by
  classical
  have key : ∀ v, ∃ x : Coords, (1 ≤ v → v ≤ TN → x ∈ tri ∧ t.f x = v) := by
    intro v
    by_cases h : 1 ≤ v ∧ v ≤ TN
    · obtain ⟨r, hr, c, hcc, hf⟩ := hsurj v h.1 h.2
      exact ⟨⟨r, c⟩, fun _ _ => ⟨mem_tri.mpr ⟨hr, hcc⟩, hf⟩⟩
    · exact ⟨⟨0, 0⟩, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose φ hφ using key
  have hinjφ : Set.InjOn φ ↑(Finset.Icc 1 TN) := by
    intro a ha b hb hab
    simp only [Finset.coe_Icc, Set.mem_Icc] at ha hb
    have e1 := (hφ a ha.1 ha.2).2
    have e2 := (hφ b hb.1 hb.2).2
    rw [hab, e2] at e1
    exact e1.symm
  have hsub : (Finset.Icc 1 TN).image φ ⊆ tri := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨v, hv, rfl⟩ := hx
    rw [Finset.mem_Icc] at hv
    exact (hφ v hv.1 hv.2).1
  have hcardimg : ((Finset.Icc 1 TN).image φ).card = TN := by
    rw [Finset.card_image_of_injOn hinjφ, Nat.card_Icc, Nat.add_sub_cancel]
  have himg_eq : (Finset.Icc 1 TN).image φ = tri :=
    Finset.eq_of_subset_of_card_le hsub (le_of_eq (by rw [card_tri, hcardimg]))
  have hsurjcell : ∀ x ∈ tri, ∃ v, 1 ≤ v ∧ v ≤ TN ∧ φ v = x := by
    intro x hx
    rw [← himg_eq, Finset.mem_image] at hx
    obtain ⟨v, hv, hvx⟩ := hx
    rw [Finset.mem_Icc] at hv
    exact ⟨v, hv.1, hv.2, hvx⟩
  refine ⟨?_, ?_⟩
  · intro x hx
    obtain ⟨v, hv1, hv2, hvx⟩ := hsurjcell x hx
    rw [← hvx, (hφ v hv1 hv2).2]
    exact ⟨hv1, hv2⟩
  · intro x hx y hy hxy
    rw [Finset.mem_coe] at hx hy
    obtain ⟨v, hv1, hv2, hvx⟩ := hsurjcell x hx
    obtain ⟨w, hw1, hw2, hwy⟩ := hsurjcell y hy
    have e1 : t.f x = v := by rw [← hvx]; exact (hφ v hv1 hv2).2
    have e2 : t.f y = w := by rw [← hwy]; exact (hφ w hw1 hw2).2
    have hvw : v = w := by rw [← e1, ← e2, hxy]
    rw [← hvx, ← hwy, hvw]

/-- The child of `x` holding the larger value. -/
private def winner (x : Coords) : Coords :=
  if t.f (left_child x) ≤ t.f (right_child x) then right_child x else left_child x

/-- The child of `x` holding the smaller value. -/
private def loser (x : Coords) : Coords :=
  if t.f (left_child x) ≤ t.f (right_child x) then left_child x else right_child x

private lemma winner_row (x : Coords) : (winner t x).row = x.row + 1 := by
  rw [winner]; split <;> rfl

private lemma loser_row (x : Coords) : (loser t x).row = x.row + 1 := by
  rw [loser]; split <;> rfl

private lemma winner_col (x : Coords) :
    (winner t x).col = x.col ∨ (winner t x).col = x.col + 1 := by
  rw [winner]; split
  · right; rfl
  · left; rfl

private lemma loser_col (x : Coords) :
    (loser t x).col = x.col ∨ (loser t x).col = x.col + 1 := by
  rw [loser]; split
  · left; rfl
  · right; rfl

/-- `winner` and `loser` are the two children, in some order. -/
private lemma winner_loser_cols (x : Coords) :
    ((winner t x).col = x.col ∧ (loser t x).col = x.col + 1) ∨
    ((winner t x).col = x.col + 1 ∧ (loser t x).col = x.col) := by
  rw [winner, loser]; split
  · right; exact ⟨rfl, rfl⟩
  · left; exact ⟨rfl, rfl⟩

private lemma loser_ne_winner (x : Coords) : loser t x ≠ winner t x := by
  rw [winner, loser]; split <;>
  · intro h; rw [left_child, right_child, Coords.mk.injEq] at h; omega

include hsurj in
/-- The defining anti-Pascal relation, oriented: `winner = parent + loser`. -/
private lemma winner_val (x : Coords) (hx : x ∈ tri) (hb : x.row + 1 < NR) :
    t.f (winner t x) = t.f x + t.f (loser t x) := by
  have hfx : 1 ≤ t.f x := ((bijection t hsurj).1 x hx).1
  have hap := t.antipascal x ⟨hb, (mem_tri.mp hx).2⟩
  by_cases hle : t.f (left_child x) ≤ t.f (right_child x)
  · rw [winner, loser, if_pos hle, if_pos hle]
    rcases hap with h | h
    · exact h.symm
    · omega
  · rw [winner, loser, if_neg hle, if_neg hle]
    rcases hap with h | h
    · omega
    · exact h.symm

/-- Children of a valid parent lie in the triangle. -/
private lemma left_child_mem {x : Coords} (hx : x ∈ tri) (hb : x.row + 1 < NR) :
    left_child x ∈ tri := by
  rw [mem_tri] at hx ⊢
  exact ⟨hb, by rw [left_child]; exact le_trans hx.2 (Nat.le_succ _)⟩

private lemma right_child_mem {x : Coords} (hx : x ∈ tri) (hb : x.row + 1 < NR) :
    right_child x ∈ tri := by
  rw [mem_tri] at hx ⊢
  refine ⟨hb, ?_⟩
  rw [right_child]
  exact Nat.succ_le_succ hx.2

private lemma winner_mem {x : Coords} (hx : x ∈ tri) (hb : x.row + 1 < NR) :
    winner t x ∈ tri := by
  rw [winner]; split
  · exact right_child_mem hx hb
  · exact left_child_mem hx hb

private lemma loser_mem {x : Coords} (hx : x ∈ tri) (hb : x.row + 1 < NR) :
    loser t x ∈ tri := by
  rw [loser]; split
  · exact left_child_mem hx hb
  · exact right_child_mem hx hb

/-- The greedy "always go to the larger child" path starting at the apex. -/
private def chain : ℕ → Coords
  | 0 => ⟨0, 0⟩
  | (i + 1) => winner t (chain i)

private lemma chain_zero : chain t 0 = ⟨0, 0⟩ := rfl

private lemma chain_succ (i : ℕ) : chain t (i + 1) = winner t (chain t i) := rfl

private lemma chain_row (i : ℕ) : (chain t i).row = i := by
  induction i with
  | zero => rfl
  | succ k ih => rw [chain_succ, winner_row, ih]

private lemma chain_mem (i : ℕ) (hi : i < NR) : chain t i ∈ tri := by
  induction i with
  | zero => rw [chain_zero, mem_tri]; exact ⟨hi, le_refl _⟩
  | succ k ih =>
      rw [chain_succ]
      exact winner_mem t (ih (by omega)) (by rw [chain_row]; exact hi)

include hsurj in
private lemma chain_step_val (k : ℕ) (hk : k + 1 < NR) :
    t.f (chain t (k + 1)) = t.f (chain t k) + t.f (loser t (chain t k)) := by
  rw [chain_succ]
  exact winner_val t hsurj (chain t k) (chain_mem t k (by omega)) (by rw [chain_row]; exact hk)

include hsurj in
private lemma chain_sum : ∀ k, k < NR →
    t.f (chain t k) = t.f (chain t 0) + ∑ i ∈ Finset.range k, t.f (loser t (chain t i)) := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ m ih =>
      intro hk
      rw [chain_step_val t hsurj m hk, ih (by omega), Finset.sum_range_succ]
      ring

/-- The smaller children dropped along the apex path (the "losers"). -/
private def losers : Finset Coords :=
  (Finset.range (NR - 1)).image (fun i => loser t (chain t i))

/-- All cells holding a value `≤ NR`: the apex together with the losers. -/
private def smallCells : Finset Coords := insert (chain t 0) (losers t)

private lemma loser_chain_row (i : ℕ) : (loser t (chain t i)).row = i + 1 := by
  rw [loser_row, chain_row]

private lemma losers_inj :
    Set.InjOn (fun i => loser t (chain t i)) ↑(Finset.range (NR - 1)) := by
  intro a _ b _ hab
  simp only [] at hab
  have h : (loser t (chain t a)).row = (loser t (chain t b)).row := by rw [hab]
  rw [loser_chain_row, loser_chain_row] at h
  omega

private lemma chain_zero_not_losers : chain t 0 ∉ losers t := by
  rw [losers, Finset.mem_image]
  rintro ⟨i, _, hi⟩
  have h : (chain t 0).row = (loser t (chain t i)).row := by rw [hi]
  rw [chain_row, loser_chain_row] at h
  omega

private lemma losers_card : (losers t).card = NR - 1 := by
  rw [losers, Finset.card_image_of_injOn (losers_inj t), Finset.card_range]

private lemma smallCells_card : (smallCells t).card = NR := by
  rw [smallCells, Finset.card_insert_of_notMem (chain_zero_not_losers t), losers_card]
  have := NR_val; omega

private lemma smallCells_subset : smallCells t ⊆ tri := by
  have hNR := NR_val
  rw [smallCells]
  intro x hx
  rw [Finset.mem_insert] at hx
  rcases hx with h | h
  · rw [h]; exact chain_mem t 0 (by omega)
  · rw [losers, Finset.mem_image] at h
    obtain ⟨i, hi, rfl⟩ := h
    rw [Finset.mem_range] at hi
    exact loser_mem t (chain_mem t i (by omega)) (by rw [chain_row]; omega)

include hsurj in
private lemma smallCells_sum :
    ∑ x ∈ smallCells t, t.f x = t.f (chain t (NR - 1)) := by
  rw [smallCells, Finset.sum_insert (chain_zero_not_losers t), losers,
      Finset.sum_image (losers_inj t)]
  have hNR := NR_val
  exact (chain_sum t hsurj (NR - 1) (by omega)).symm

include hsurj in
private lemma smallCells_injOn : Set.InjOn t.f ↑(smallCells t) :=
  (bijection t hsurj).2.mono (Finset.coe_subset.mpr (smallCells_subset t))

include hsurj in
private lemma chain_bottom : t.f (chain t (NR - 1)) = TN := by
  have hNR := NR_val
  have hsumV : ∑ v ∈ (smallCells t).image t.f, v = t.f (chain t (NR - 1)) := by
    rw [Finset.sum_image (smallCells_injOn t hsurj)]
    exact smallCells_sum t hsurj
  have hpos : ∀ x ∈ (smallCells t).image t.f, 1 ≤ x := by
    intro v hv
    rw [Finset.mem_image] at hv
    obtain ⟨x, hx, rfl⟩ := hv
    exact ((bijection t hsurj).1 x (smallCells_subset t hx)).1
  have hcard : ((smallCells t).image t.f).card = NR := by
    rw [Finset.card_image_of_injOn (smallCells_injOn t hsurj), smallCells_card]
  have hle : t.f (chain t (NR - 1)) ≤ TN :=
    ((bijection t hsurj).1 _ (chain_mem t (NR - 1) (by omega))).2
  have hmin := min_sum ((smallCells t).image t.f) hpos
  rw [hcard, TN_def, hsumV] at hmin
  omega

include hsurj in
private lemma smallCells_image : (smallCells t).image t.f = Finset.Icc 1 NR := by
  have hpos : ∀ x ∈ (smallCells t).image t.f, 1 ≤ x := by
    intro v hv
    rw [Finset.mem_image] at hv
    obtain ⟨x, hx, rfl⟩ := hv
    exact ((bijection t hsurj).1 x (smallCells_subset t hx)).1
  have hcard : ((smallCells t).image t.f).card = NR := by
    rw [Finset.card_image_of_injOn (smallCells_injOn t hsurj), smallCells_card]
  have hsumV : ∑ v ∈ (smallCells t).image t.f, v = t.f (chain t (NR - 1)) := by
    rw [Finset.sum_image (smallCells_injOn t hsurj)]
    exact smallCells_sum t hsurj
  have heq := min_sum_eq ((smallCells t).image t.f) hpos
    (by rw [hcard, TN_def, hsumV, chain_bottom t hsurj])
  rw [heq, hcard]

include hsurj in
/-- Every cell outside the band of small cells holds a value `> NR`. -/
private lemma not_small (x : Coords) (hx : x ∈ tri) (hxs : x ∉ smallCells t) :
    NR < t.f x := by
  by_contra hcon
  push Not at hcon
  have hxb := (bijection t hsurj).1 x hx
  have : t.f x ∈ (smallCells t).image t.f := by
    rw [smallCells_image t hsurj, Finset.mem_Icc]; exact ⟨hxb.1, hcon⟩
  rw [Finset.mem_image] at this
  obtain ⟨y, hy, hyx⟩ := this
  have hyx' : y = x := (bijection t hsurj).2
    (Finset.mem_coe.mpr (smallCells_subset t hy)) (Finset.mem_coe.mpr hx) hyx
  rw [hyx'] at hy
  exact hxs hy

/-! ### Column monotonicity of the apex path -/

private lemma chain_col_le_succ (r : ℕ) : (chain t r).col ≤ (chain t (r + 1)).col := by
  rw [chain_succ]; rcases winner_col t (chain t r) with h | h <;> omega

private lemma chain_col_succ_le (r : ℕ) : (chain t (r + 1)).col ≤ (chain t r).col + 1 := by
  rw [chain_succ]; rcases winner_col t (chain t r) with h | h <;> omega

private lemma chain_col_mono {a b : ℕ} (hab : a ≤ b) :
    (chain t a).col ≤ (chain t b).col := by
  induction b, hab using Nat.le_induction with
  | base => exact le_refl _
  | succ n _ ih => exact le_trans ih (chain_col_le_succ t n)

private lemma chain_col_le_add {a b : ℕ} (hab : a ≤ b) :
    (chain t b).col ≤ (chain t a).col + (b - a) := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
      have := chain_col_succ_le t n
      omega

/-! ### Locations of small cells (the band) -/

private lemma notMem_small_left (r j : ℕ) (hr : 1 ≤ r) (hj : j < (chain t (r - 1)).col) :
    (⟨r, j⟩ : Coords) ∉ smallCells t := by
  rw [smallCells, Finset.mem_insert]
  push Not
  refine ⟨?_, ?_⟩
  · intro h; rw [chain_zero, Coords.mk.injEq] at h; omega
  · rw [losers, Finset.mem_image]
    push Not
    intro i _ heq
    have hrow : i + 1 = r := by
      have h := congrArg Coords.row heq; rw [loser_chain_row] at h; exact h
    subst hrow
    rw [Nat.add_sub_cancel] at hj
    have hcol : (loser t (chain t i)).col = j := by rw [heq]
    rcases loser_col t (chain t i) with h | h <;> (rw [h] at hcol; omega)

private lemma notMem_small_right (r j : ℕ) (hr : 1 ≤ r)
    (hj : (chain t (r - 1)).col + 1 < j) : (⟨r, j⟩ : Coords) ∉ smallCells t := by
  rw [smallCells, Finset.mem_insert]
  push Not
  refine ⟨?_, ?_⟩
  · intro h; rw [chain_zero, Coords.mk.injEq] at h; omega
  · rw [losers, Finset.mem_image]
    push Not
    intro i _ heq
    have hrow : i + 1 = r := by
      have h := congrArg Coords.row heq; rw [loser_chain_row] at h; exact h
    subst hrow
    rw [Nat.add_sub_cancel] at hj
    have hcol : (loser t (chain t i)).col = j := by rw [heq]
    rcases loser_col t (chain t i) with h | h <;> (rw [h] at hcol; omega)

/-! ### A downward sub-triangle and the second path -/

/-- A winner-path starting from an arbitrary cell. -/
private def walk (s : Coords) : ℕ → Coords
  | 0 => s
  | (k + 1) => winner t (walk s k)

private lemma walk_zero (s : Coords) : walk t s 0 = s := rfl

private lemma walk_succ (s : Coords) (k : ℕ) : walk t s (k + 1) = winner t (walk t s k) := rfl

private lemma walk_row (s : Coords) (k : ℕ) : (walk t s k).row = s.row + k := by
  induction k with
  | zero => rfl
  | succ m ih => rw [walk_succ, winner_row, ih]; omega

include hsurj in
private lemma walk_sum (s : Coords) (L : ℕ)
    (hmem : ∀ k, k < L → walk t s k ∈ tri ∧ (walk t s k).row + 1 < NR) :
    t.f (walk t s L) = t.f s + ∑ k ∈ Finset.range L, t.f (loser t (walk t s k)) := by
  induction L with
  | zero => simp [walk_zero]
  | succ m ih =>
      rw [walk_succ,
          winner_val t hsurj (walk t s m) (hmem m (by omega)).1 (hmem m (by omega)).2,
          ih (fun k hk => hmem k (by omega)), Finset.sum_range_succ]
      ring

/-- Membership in the downward sub-triangle with apex `(p, q)`. -/
private def inSub (p q : ℕ) (x : Coords) : Prop :=
  p ≤ x.row ∧ x.row ≤ NR - 1 ∧ q ≤ x.col ∧ x.col ≤ q + (x.row - p)

private lemma inSub_left {p q : ℕ} {x : Coords} (h : inSub p q x) (hx : x.row < NR - 1) :
    inSub p q (left_child x) := by
  simp only [inSub, left_child] at h ⊢
  omega

private lemma inSub_right {p q : ℕ} {x : Coords} (h : inSub p q x) (hx : x.row < NR - 1) :
    inSub p q (right_child x) := by
  simp only [inSub, right_child] at h ⊢
  omega

private lemma inSub_winner {p q : ℕ} {x : Coords} (h : inSub p q x) (hx : x.row < NR - 1) :
    inSub p q (winner t x) := by
  rw [winner]; split
  · exact inSub_right h hx
  · exact inSub_left h hx

private lemma inSub_loser {p q : ℕ} {x : Coords} (h : inSub p q x) (hx : x.row < NR - 1) :
    inSub p q (loser t x) := by
  rw [loser]; split
  · exact inSub_left h hx
  · exact inSub_right h hx

private lemma walk_inSub (p q : ℕ) (hp : p ≤ NR - 1) :
    ∀ k, k ≤ NR - 1 - p → inSub p q (walk t ⟨p, q⟩ k) := by
  intro k
  induction k with
  | zero =>
      intro _
      refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [walk_zero] <;> omega
  | succ m ih =>
      intro hk
      rw [walk_succ]
      refine inSub_winner t (ih (by omega)) ?_
      have hr : (walk t ⟨p, q⟩ m).row = p + m := walk_row t ⟨p, q⟩ m
      rw [hr]; omega

include hsurj in
/-- A downward sub-triangle disjoint from the small cells, reaching `≥ 1007` rows down,
yields a contradiction: its winner-path picks up `≥ 1007` distinct losers all `> NR`. -/
private lemma corner_contra (p q : ℕ) (hp : p ≤ NR - 1)
    (hsub : ∀ x : Coords, inSub p q x → x ∈ tri ∧ x ∉ smallCells t)
    (hlen : 1007 ≤ NR - 1 - p) : False := by
  have hNR := NR_val
  have hwr : ∀ k, (walk t ⟨p, q⟩ k).row = p + k := fun k => walk_row t ⟨p, q⟩ k
  have hin : ∀ k, k ≤ NR - 1 - p → inSub p q (walk t ⟨p, q⟩ k) := walk_inSub t p q hp
  set L := NR - 1 - p with hLdef
  have hmemv : ∀ k, k < L → walk t ⟨p, q⟩ k ∈ tri ∧ (walk t ⟨p, q⟩ k).row + 1 < NR := by
    intro k hk
    exact ⟨(hsub _ (hin k (by omega))).1, by rw [hwr]; omega⟩
  have hsum := walk_sum t hsurj ⟨p, q⟩ L hmemv
  have hbig : ∀ k, k < L → NR < t.f (loser t (walk t ⟨p, q⟩ k)) := by
    intro k hk
    refine not_small t hsurj _ ?_ ?_
    · exact loser_mem t (hsub _ (hin k (by omega))).1 (by rw [hwr]; omega)
    · exact (hsub _ (inSub_loser t (hin k (by omega)) (by rw [hwr]; omega))).2
  have hvinj : Set.InjOn (fun k => t.f (loser t (walk t ⟨p, q⟩ k))) ↑(Finset.range L) := by
    intro a ha b hb hab
    rw [Finset.coe_range, Set.mem_Iio] at ha hb
    simp only [] at hab
    have hla : loser t (walk t ⟨p, q⟩ a) ∈ tri :=
      loser_mem t (hsub _ (hin a (by omega))).1 (by rw [hwr]; omega)
    have hlb : loser t (walk t ⟨p, q⟩ b) ∈ tri :=
      loser_mem t (hsub _ (hin b (by omega))).1 (by rw [hwr]; omega)
    have hcell := (bijection t hsurj).2 (Finset.mem_coe.mpr hla) (Finset.mem_coe.mpr hlb) hab
    have hrows : (loser t (walk t ⟨p, q⟩ a)).row = (loser t (walk t ⟨p, q⟩ b)).row := by rw [hcell]
    rw [loser_row, loser_row, hwr, hwr] at hrows
    omega
  set V0 := (Finset.range L).image (fun k => t.f (loser t (walk t ⟨p, q⟩ k))) with hV0
  have hV0card : V0.card = L := by rw [hV0, Finset.card_image_of_injOn hvinj, Finset.card_range]
  have hV0pos : ∀ x ∈ V0, NR < x := by
    intro x hx; rw [hV0, Finset.mem_image] at hx
    obtain ⟨k, hk, rfl⟩ := hx; rw [Finset.mem_range] at hk; exact hbig k hk
  have hsumV0 : ∑ x ∈ V0, x = ∑ k ∈ Finset.range L, t.f (loser t (walk t ⟨p, q⟩ k)) := by
    rw [hV0, Finset.sum_image hvinj]
  have hlb := min_sum_ge V0 NR hV0pos
  rw [hV0card, hsumV0] at hlb
  have hwalkL : walk t ⟨p, q⟩ L ∈ tri := (hsub _ (hin L (le_refl _))).1
  have hub : t.f (walk t ⟨p, q⟩ L) ≤ TN := ((bijection t hsurj).1 _ hwalkL).2
  have hmono : ∑ i ∈ Finset.range 1007, (i + 1) ≤ ∑ i ∈ Finset.range L, (i + 1) :=
    Finset.sum_le_sum_of_subset (by intro x hx; rw [Finset.mem_range] at hx ⊢; omega)
  have h1007 := two_mul_sum 1007
  have hTNval : TN = 2037171 := by
    have h := two_mul_sum NR; rw [TN_def, NR_val] at h; omega
  have hlb' : L * 2018 + ∑ i ∈ Finset.range L, (i + 1) ≤
      ∑ k ∈ Finset.range L, t.f (loser t (walk t ⟨p, q⟩ k)) := by
    have he : L * NR = L * 2018 := by rw [NR_val]
    rw [← he]; exact hlb
  omega

include hsurj in
private lemma not_exists_desired : False := by
  have hNR := NR_val
  set c := (chain t (NR - 2)).col with hc
  have hcle : c ≤ NR - 2 := by
    rw [hc]
    have h := (mem_tri.mp (chain_mem t (NR - 2) (by omega))).2
    rw [chain_row] at h; exact h
  by_cases hcase : 1008 ≤ c
  · -- Left corner: apex `(NR - c, 0)`.
    refine corner_contra t hsurj (NR - c) 0 (by omega) ?_ (by omega)
    intro x hx
    simp only [inSub] at hx
    obtain ⟨hr1, hr2, _, hc4⟩ := hx
    have hxcol : x.col ≤ x.row := by omega
    refine ⟨mem_tri.mpr ⟨by omega, hxcol⟩, ?_⟩
    have hadd : c ≤ (chain t (x.row - 1)).col + ((NR - 2) - (x.row - 1)) := by
      rw [hc]; exact chain_col_le_add t (by omega)
    exact notMem_small_left t x.row x.col (by omega) (by omega)
  · -- Right corner: apex `(c + 2, c + 2)`.
    push Not at hcase
    refine corner_contra t hsurj (c + 2) (c + 2) (by omega) ?_ (by omega)
    intro x hx
    simp only [inSub] at hx
    obtain ⟨hr1, hr2, hc3, hc4⟩ := hx
    have hxcol : x.col ≤ x.row := by omega
    refine ⟨mem_tri.mpr ⟨by omega, hxcol⟩, ?_⟩
    have hmono : (chain t (x.row - 1)).col ≤ c := by
      rw [hc]; exact chain_col_mono t (by omega)
    exact notMem_small_right t x.row x.col (by omega) (by omega)

end

snip end

determine does_exist : Bool := false

problem imo2018_p3 : does_exist ↔ exists_desired_triangle := by
  simp only [exists_desired_triangle, Bool.false_eq_true, false_iff]
  rintro ⟨t, ht⟩
  exact not_exists_desired t ht


end Imo2018P3
