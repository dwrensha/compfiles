/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Tactic.IntervalCases
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Olympiad 2000, Problem 4

100 cards are numbered 1 to 100 (each card different) and placed in 3 boxes
(at least one card in each box). How many ways can this be done so that if
two boxes are selected and a card is taken from each, then the knowledge of
their sum alone is always sufficient to identify the third box?
-/

namespace Imo2000P4

snip begin

/-!
### Proof sketch

We follow the solution from <https://prase.cz/kalva/imo/isoln/isoln004.html>.

The boxes are labeled by `ZMod 3` and a placement of the cards `1, ..., n` is a
function `f : ℕ → ZMod 3`. Being able to identify the third box from the sum of
two cards drawn from two different boxes is equivalent to: whenever two pairs of
cards from two different pairs of boxes have equal sums, the two pairs of boxes
coincide (`GoodPlacement`; the equivalence is `valid_iff_good`).

The valid placements of `1, ..., n` (for `3 ≤ n`) are exactly:
* the placements by residue mod 3 (`Mod3`), and
* the placements with cards `1` and `n` alone in two boxes and `2, ..., n-1` in
  the third box (`Ends`).

This is proved by induction on `n` (`classify`): if `n + 1` is alone in its box,
then `1` must be alone too, giving an `Ends` placement; otherwise removing
`n + 1` gives a valid placement of `n` cards, and the induction hypothesis
leaves only the `Mod3` possibility.

For `n = 100` each family has `3! = 6` elements and they are disjoint,
so the answer is `12`.
-/

/-- A placement of the cards `1, ..., n` into three boxes (labeled by `ZMod 3`)
is *good* if every box is nonempty and whenever two pairs of cards from two
different pairs of boxes have the same sum, the pairs of boxes coincide. -/
def Good (n : ℕ) (f : ℕ → ZMod 3) : Prop :=
  (∀ b : ZMod 3, ∃ a, 1 ≤ a ∧ a ≤ n ∧ f a = b) ∧
  ∀ a b c d : ℕ, 1 ≤ a → a ≤ n → 1 ≤ b → b ≤ n → 1 ≤ c → c ≤ n → 1 ≤ d → d ≤ n →
    f a ≠ f b → f c ≠ f d → a + b = c + d →
    (f a = f c ∧ f b = f d) ∨ (f a = f d ∧ f b = f c)

/-- The mod-3 placements: the box of card `a` depends only on `a % 3`. -/
def Mod3 (n : ℕ) (f : ℕ → ZMod 3) : Prop :=
  ∃ σ : Equiv.Perm (ZMod 3), ∀ a, 1 ≤ a → a ≤ n → f a = σ (a : ZMod 3)

/-- The "ends" placements: cards `1` and `n` are alone in two boxes and all
cards `2, ..., n - 1` are in the third box. -/
def Ends (n : ℕ) (f : ℕ → ZMod 3) : Prop :=
  ∃ σ : Equiv.Perm (ZMod 3), f 1 = σ 0 ∧ f n = σ 1 ∧
    ∀ a, 2 ≤ a → a ≤ n - 1 → f a = σ 2

lemma exists_third (x y : ZMod 3) : ∃ z, z ≠ x ∧ z ≠ y := by
  revert x y; decide

lemma eq_third {x y z w : ZMod 3} (hxy : x ≠ y) (hzx : z ≠ x) (hzy : z ≠ y)
    (hwx : w ≠ x) (hwy : w ≠ y) : w = z := by
  fin_cases x <;> fin_cases y <;> fin_cases z <;> fin_cases w <;> simp_all

lemma equiv_of_distinct {x y z : ZMod 3} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ∃ σ : Equiv.Perm (ZMod 3), x = σ 0 ∧ y = σ 1 ∧ z = σ 2 := by
  have hinj : Function.Injective ![x, y, z] := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all
  refine ⟨Equiv.ofBijective ![x, y, z] (Finite.injective_iff_bijective.mp hinj),
    ?_, ?_, ?_⟩ <;> simp

lemma tri (r : ZMod 3) : r = 0 ∨ r = 1 ∨ r = 2 := by
  revert r; decide

lemma pair_eq_of_sum_aux : ∀ x y z w : ZMod 3, x ≠ y → z ≠ w → x + y = z + w →
    (x = z ∧ y = w) ∨ (x = w ∧ y = z) := by decide

lemma pair_eq_of_sum {x y z w : ZMod 3} (hxy : x ≠ y) (hzw : z ≠ w)
    (h : x + y = z + w) : (x = z ∧ y = w) ∨ (x = w ∧ y = z) :=
  pair_eq_of_sum_aux x y z w hxy hzw h

lemma cast_ne_add_one_two (k : ℕ) {r : ℕ} (hr : r = 1 ∨ r = 2) :
    (k : ZMod 3) ≠ ((k + r : ℕ) : ZMod 3) := by
  rcases hr with rfl | rfl
  · rw [Nat.cast_add, Nat.cast_one]
    intro h
    have h2 : (k : ZMod 3) + 0 = (k : ZMod 3) + 1 := by rw [add_zero]; exact h
    exact (by decide : (0 : ZMod 3) ≠ 1) (add_left_cancel h2)
  · rw [Nat.cast_add, Nat.cast_ofNat]
    intro h
    have h2 : (k : ZMod 3) + 0 = (k : ZMod 3) + 2 := by rw [add_zero]; exact h
    exact (by decide : (0 : ZMod 3) ≠ 2) (add_left_cancel h2)

/-- If `n + 1` shares its box with another card, then a good placement of
`1, ..., n + 1` restricts to a good placement of `1, ..., n`. -/
lemma good_mono {n : ℕ} {f : ℕ → ZMod 3} (hf : Good (n + 1) f)
    (h : ∃ m, 1 ≤ m ∧ m ≤ n ∧ f m = f (n + 1)) : Good n f := by
  obtain ⟨m, hm1, hmn, hfm⟩ := h
  constructor
  · intro b
    obtain ⟨a, ha1, ha2, hfa⟩ := hf.1 b
    by_cases han : a ≤ n
    · exact ⟨a, ha1, han, hfa⟩
    · have haeq : a = n + 1 := by omega
      exact ⟨m, hm1, hmn, by rw [hfm, ← haeq]; exact hfa⟩
  · intro a b c d ha1 ha2 hb1 hb2 hc1 hc2 hd1 hd2 hab hcd hsum
    exact hf.2 a b c d ha1 (by omega) hb1 (by omega) hc1 (by omega) hd1 (by omega)
      hab hcd hsum

/-- Case 1 of the induction step: `n + 1` is alone in its box. Then `1` is also
alone, and we get an `Ends` placement. -/
lemma case_alone {n : ℕ} (hn : 3 ≤ n) {f : ℕ → ZMod 3} (hf : Good (n + 1) f)
    (halone : ∀ a, 1 ≤ a → a ≤ n → f a ≠ f (n + 1)) : Ends (n + 1) f := by
  have hn1 : 1 ≤ n := by omega
  have h1n : f 1 ≠ f (n + 1) := halone 1 le_rfl hn1
  -- `1` is also alone in its box.
  have claimA : ∀ a, 2 ≤ a → a ≤ n + 1 → f a ≠ f 1 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨m, hm1, hm2, hfm⟩ := hcon
    have hmn : m ≤ n := by
      by_contra h
      have hmeq : m = n + 1 := by omega
      rw [hmeq] at hfm
      exact h1n hfm.symm
    -- Find a card `y ≥ 2` in a different box than `n`.
    have hfn : f n ≠ f (n + 1) := halone n hn1 le_rfl
    obtain ⟨z, hz1, hz2⟩ := exists_third (f (n + 1)) (f n)
    obtain ⟨a, ha1, ha2, hfa⟩ := hf.1 z
    have han : a ≤ n := by
      by_contra h
      have haeq : a = n + 1 := by omega
      rw [haeq] at hfa
      exact hz1 hfa.symm
    have hann : a ≠ n := by
      intro h
      rw [h] at hfa
      exact hz2 hfa.symm
    obtain ⟨y, hy2, hyn, hfy⟩ : ∃ y, 2 ≤ y ∧ y ≤ n - 1 ∧ f y ≠ f n := by
      by_cases ha : 2 ≤ a
      · exact ⟨a, ha, by omega, by rw [hfa]; exact hz2⟩
      · have ha1' : a = 1 := by omega
        have hf1 : f 1 = z := ha1' ▸ hfa
        have hmn' : m ≤ n - 1 := by
          by_contra h
          have hm : m = n := by omega
          exact hz2 (hm ▸ (hfm.trans hf1)).symm
        exact ⟨m, hm1, hmn', fun h ↦ hz2 ((hfm.trans hf1).symm.trans h)⟩
    -- The pairs `(n, y)` and `(n + 1, y - 1)` have equal sums but their boxes
    -- do not match: contradiction.
    have hy1 : 1 ≤ y - 1 := by omega
    have hyn2 : y - 1 ≤ n := by omega
    have hsum : n + y = (n + 1) + (y - 1) := by omega
    have hcd : f (n + 1) ≠ f (y - 1) := (halone (y - 1) hy1 hyn2).symm
    rcases hf.2 n y (n + 1) (y - 1) hn1 (by omega) (by omega) (by omega)
        (by omega) le_rfl (by omega) (by omega) hfy.symm hcd hsum with
      ⟨hA1, -⟩ | ⟨-, hB2⟩
    · exact hfn hA1
    · exact halone y (by omega) (by omega) hB2
  obtain ⟨z, hz1, hz2⟩ := exists_third (f 1) (f (n + 1))
  obtain ⟨σ, hσ0, hσ1, hσ2⟩ := equiv_of_distinct h1n hz1.symm hz2.symm
  refine ⟨σ, hσ0, hσ1, fun a h2a h3a ↦ ?_⟩
  have han : a ≤ n := by omega
  have hfa1 : f a ≠ f 1 := claimA a h2a (by omega)
  have hfa2 : f a ≠ f (n + 1) := halone a (by omega) han
  have haz : f a = z := eq_third h1n hz1 hz2 hfa1 hfa2
  rw [← hσ2]; exact haz

/-- Case 2a of the induction step: the restriction to `1, ..., n` is a mod-3
placement; then `n + 1` must go into the box of its own residue. -/
lemma case_mod3 {n : ℕ} (hn : 3 ≤ n) {f : ℕ → ZMod 3} (hf : Good (n + 1) f)
    (hm : Mod3 n f) : Mod3 (n + 1) f := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  have hk : 1 ≤ k := by omega
  obtain ⟨σ, hσ⟩ := hm
  have hf' : Good (k + 3) f := hf
  have r01 : (k : ZMod 3) ≠ ((k + 1 : ℕ) : ZMod 3) :=
    cast_ne_add_one_two k (Or.inl rfl)
  have r02 : (k : ZMod 3) ≠ ((k + 2 : ℕ) : ZMod 3) :=
    cast_ne_add_one_two k (Or.inr rfl)
  have r12 : ((k + 1 : ℕ) : ZMod 3) ≠ ((k + 2 : ℕ) : ZMod 3) :=
    cast_ne_add_one_two (k + 1) (Or.inl rfl)
  have fk : f k = σ (k : ZMod 3) := hσ k hk (by omega)
  have fk1 : f (k + 1) = σ ((k + 1 : ℕ) : ZMod 3) := hσ (k + 1) (by omega) (by omega)
  have fk2 : f (k + 2) = σ ((k + 2 : ℕ) : ZMod 3) := hσ (k + 2) (by omega) (by omega)
  have d01 : f k ≠ f (k + 1) := by rw [fk, fk1]; exact σ.injective.ne_iff.mpr r01
  have d02 : f k ≠ f (k + 2) := by rw [fk, fk2]; exact σ.injective.ne_iff.mpr r02
  have d12 : f (k + 1) ≠ f (k + 2) := by rw [fk1, fk2]; exact σ.injective.ne_iff.mpr r12
  -- The pairs `(k + 3, k)` and `(k + 2, k + 1)` have equal sums, so `k + 3`
  -- shares its box with `k`.
  have key : f (k + 3) = f k := by
    by_contra hne
    have hsum : (k + 3) + k = (k + 2) + (k + 1) := by omega
    rcases hf'.2 (k + 3) k (k + 2) (k + 1) (by omega) le_rfl (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) hne d12.symm hsum with
      ⟨-, h2⟩ | ⟨-, h2⟩
    · exact d01 h2
    · exact d02 h2
  have hcast : ((k + 3 : ℕ) : ZMod 3) = (k : ZMod 3) := by
    rw [Nat.cast_add, ZMod.natCast_self, add_zero]
  refine ⟨σ, fun a h1a h2a ↦ ?_⟩
  by_cases ha : a ≤ k + 2
  · exact hσ a h1a ha
  · have ha' : a = k + 3 := by omega
    rw [ha', hcast]
    exact key.trans fk

/-- Case 2b of the induction step: the restriction to `1, ..., n` is an `Ends`
placement with `4 ≤ n`; then there is no room for the card `n + 1`. -/
lemma case_ends {n : ℕ} (hn : 4 ≤ n) {f : ℕ → ZMod 3} (hf : Good (n + 1) f)
    (he : Ends n f) : False := by
  obtain ⟨σ, h0, h1, h2⟩ := he
  have hf2 : f 2 = σ 2 := h2 2 le_rfl (by omega)
  have hf3 : f 3 = σ 2 := h2 3 (by norm_num) (by omega)
  have s01 : σ 0 ≠ σ 1 := σ.injective.ne_iff.mpr (by decide)
  have s02 : σ 0 ≠ σ 2 := σ.injective.ne_iff.mpr (by decide)
  have s12 : σ 1 ≠ σ 2 := σ.injective.ne_iff.mpr (by decide)
  obtain ⟨i, hi⟩ := σ.surjective (f (n + 1))
  rcases tri i with rfl | rfl | rfl
  · -- `f (n + 1) = σ 0 = f 1`: use the pairs `(n + 1, 2)` and `(n, 3)`.
    have hab : f (n + 1) ≠ f 2 := by rw [← hi, hf2]; exact s02
    have hcd : f n ≠ f 3 := by rw [h1, hf3]; exact s12
    rcases hf.2 (n + 1) 2 n 3 (by omega) le_rfl (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) hab hcd (by omega) with ⟨hA1, -⟩ | ⟨hB1, -⟩
    · rw [← hi, h1] at hA1; exact s01 hA1
    · rw [← hi, hf3] at hB1; exact s02 hB1
  · -- `f (n + 1) = σ 1 = f n`: use the pairs `(n + 1, 1)` and `(n, 2)`.
    have hab : f (n + 1) ≠ f 1 := by rw [← hi, h0]; exact s01.symm
    have hcd : f n ≠ f 2 := by rw [h1, hf2]; exact s12
    rcases hf.2 (n + 1) 1 n 2 (by omega) le_rfl (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) hab hcd (by omega) with ⟨-, hA2⟩ | ⟨hB1, -⟩
    · rw [h0, hf2] at hA2; exact s02 hA2
    · rw [← hi, hf2] at hB1; exact s12 hB1
  · -- `f (n + 1) = σ 2`: use the pairs `(n + 1, 1)` and `(n, 2)`.
    have hab : f (n + 1) ≠ f 1 := by rw [← hi, h0]; exact s02.symm
    have hcd : f n ≠ f 2 := by rw [h1, hf2]; exact s12
    rcases hf.2 (n + 1) 1 n 2 (by omega) le_rfl (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) hab hcd (by omega) with ⟨hA1, -⟩ | ⟨-, hB2⟩
    · rw [← hi, h1] at hA1; exact s12.symm hA1
    · rw [h0, h1] at hB2; exact s01 hB2

/-- Base case: every good placement of `1, 2, 3` puts the three cards in
three different boxes. -/
lemma base_case {f : ℕ → ZMod 3} (hf : Good 3 f) : Ends 3 f := by
  have d12 : f 1 ≠ f 2 := by
    intro h
    obtain ⟨z, hz1, hz2⟩ := exists_third (f 1) (f 3)
    obtain ⟨a, ha1, ha2, hfa⟩ := hf.1 z
    interval_cases a
    · exact hz1 hfa.symm
    · rw [← h] at hfa; exact hz1 hfa.symm
    · exact hz2 hfa.symm
  have d23 : f 2 ≠ f 3 := by
    intro h
    obtain ⟨z, hz1, hz2⟩ := exists_third (f 1) (f 3)
    obtain ⟨a, ha1, ha2, hfa⟩ := hf.1 z
    interval_cases a
    · exact hz1 hfa.symm
    · rw [h] at hfa; exact hz2 hfa.symm
    · exact hz2 hfa.symm
  have d13 : f 1 ≠ f 3 := by
    intro h
    obtain ⟨z, hz1, hz2⟩ := exists_third (f 1) (f 2)
    obtain ⟨a, ha1, ha2, hfa⟩ := hf.1 z
    interval_cases a
    · exact hz1 hfa.symm
    · exact hz2 hfa.symm
    · rw [← h] at hfa; exact hz1 hfa.symm
  obtain ⟨σ, h0, h1, h2⟩ := equiv_of_distinct d13 d12 d23.symm
  exact ⟨σ, h0, h1, fun a h2a h3a ↦ by
    have ha : a = 2 := by omega
    rw [ha]; exact h2⟩

/-- For `n = 3` the two families coincide. -/
lemma ends3_mod3 {f : ℕ → ZMod 3} (he : Ends 3 f) : Mod3 3 f := by
  obtain ⟨σ, h0, h1, h2⟩ := he
  have hf2 : f 2 = σ 2 := h2 2 le_rfl (by norm_num)
  have e31 : f 3 ≠ f 1 := by rw [h1, h0]; exact σ.injective.ne_iff.mpr (by decide)
  have e32 : f 3 ≠ f 2 := by rw [h1, hf2]; exact σ.injective.ne_iff.mpr (by decide)
  have e12 : f 1 ≠ f 2 := by rw [h0, hf2]; exact σ.injective.ne_iff.mpr (by decide)
  obtain ⟨τ, t0, t1, t2⟩ := equiv_of_distinct e31 e32 e12
  refine ⟨τ, fun a h1a h2a ↦ ?_⟩
  interval_cases a
  · rw [Nat.cast_one]; exact t1
  · rw [Nat.cast_ofNat]; exact t2
  · rw [ZMod.natCast_self]; exact t0

/-- The classification: every good placement of `1, ..., n` (`3 ≤ n`) is either
by residue mod 3 or an `Ends` placement. -/
lemma classify (n : ℕ) (hn : 3 ≤ n) (f : ℕ → ZMod 3) :
    Good n f → Mod3 n f ∨ Ends n f := by
  induction n, hn using Nat.le_induction with
  | base =>
      intro hf
      exact Or.inr (base_case hf)
  | succ n hn ih =>
      intro hf
      by_cases halone : ∀ a, 1 ≤ a → a ≤ n → f a ≠ f (n + 1)
      · exact Or.inr (case_alone hn hf halone)
      · push Not at halone
        obtain ⟨m, hm1, hmn, hfm⟩ := halone
        have hgood : Good n f := good_mono hf ⟨m, hm1, hmn, hfm⟩
        rcases ih hgood with hmod | hends
        · exact Or.inl (case_mod3 hn hf hmod)
        · rcases Nat.eq_or_lt_of_le hn with h3 | h4
          · subst h3
            exact Or.inl (case_mod3 (le_refl 3) hf (ends3_mod3 hends))
          · exact (case_ends h4 hf hends).elim

snip end

/-- A placement of the 100 cards into 3 boxes (labeled by `ZMod 3`) is *valid*
if every box is nonempty and whenever two boxes are selected and a card is
taken from each, the sum of the two drawn cards always suffices to identify
the third box: any two such selections of two distinct boxes and two cards
with the same sum leave the same box unselected.
Card `i + 1` is represented by the index `i : Fin 100`. -/
def ValidPlacement (f : Fin 100 → ZMod 3) : Prop :=
  Function.Surjective f ∧
  ∀ i j k l : Fin 100, f i ≠ f j → f k ≠ f l →
    (i : ℕ) + 1 + ((j : ℕ) + 1) = (k : ℕ) + 1 + ((l : ℕ) + 1) →
    ∀ b : ZMod 3, (b ≠ f i ∧ b ≠ f j) ↔ (b ≠ f k ∧ b ≠ f l)

snip begin

/-- Combinatorial form of validity: whenever two pairs of cards from two
different pairs of boxes have the same sum of indices, the pairs of boxes
coincide. Equivalent to `ValidPlacement` (`valid_iff_good`); this is the form
used in the classification argument. -/
def GoodPlacement (f : Fin 100 → ZMod 3) : Prop :=
  Function.Surjective f ∧
  ∀ i j k l : Fin 100, f i ≠ f j → f k ≠ f l → (i : ℕ) + j = (k : ℕ) + l →
    (f i = f k ∧ f j = f l) ∨ (f i = f l ∧ f j = f k)

/-- Two pairs of distinct boxes leave the same third box unselected if and
only if the two pairs of boxes coincide. -/
lemma third_box_iff_pair {x y z w : ZMod 3} (hxy : x ≠ y) (hzw : z ≠ w) :
    (∀ b : ZMod 3, (b ≠ x ∧ b ≠ y) ↔ (b ≠ z ∧ b ≠ w)) ↔
      (x = z ∧ y = w) ∨ (x = w ∧ y = z) := by
  revert x y z w
  decide

/-- The olympiad formulation of validity is equivalent to its combinatorial
form: the sum of two cards drawn from two different boxes determines the
third box iff equal sums force the two pairs of boxes to coincide. -/
lemma valid_iff_good (f : Fin 100 → ZMod 3) :
    ValidPlacement f ↔ GoodPlacement f := by
  constructor <;> rintro ⟨hsurj, h⟩ <;> refine ⟨hsurj, fun i j k l hij hkl hsum ↦ ?_⟩
  · exact (third_box_iff_pair hij hkl).mp
      (h i j k l hij hkl (by omega : (i : ℕ) + 1 + ((j : ℕ) + 1) =
        (k : ℕ) + 1 + ((l : ℕ) + 1)))
  · exact (third_box_iff_pair hij hkl).mpr
      (h i j k l hij hkl (by omega : (i : ℕ) + j = (k : ℕ) + l))

/-- Extend a placement `g : Fin 100 → ZMod 3` to all of `ℕ` (by `0` outside
`[1, 100]`); card `a` corresponds to index `a - 1`. -/
def lift (g : Fin 100 → ZMod 3) (a : ℕ) : ZMod 3 :=
  if h : 1 ≤ a ∧ a ≤ 100 then g ⟨a - 1, by omega⟩ else 0

lemma lift_apply (g : Fin 100 → ZMod 3) {a : ℕ} (h1 : 1 ≤ a) (h2 : a ≤ 100) :
    lift g a = g ⟨a - 1, by omega⟩ := dif_pos ⟨h1, h2⟩

lemma lift_apply_fin (g : Fin 100 → ZMod 3) (i : Fin 100) : lift g (↑i + 1) = g i := by
  rw [lift_apply g (a := ↑i + 1) (by omega) (by omega)]
  exact congrArg g (Fin.ext (show (↑i : ℕ) + 1 - 1 = (i : ℕ) by omega))

lemma lift_good {g : Fin 100 → ZMod 3} (hg : GoodPlacement g) : Good 100 (lift g) := by
  constructor
  · intro b
    obtain ⟨i, hi⟩ := hg.1 b
    exact ⟨↑i + 1, by omega, by omega, by rw [lift_apply_fin]; exact hi⟩
  · intro a b c d ha1 ha2 hb1 hb2 hc1 hc2 hd1 hd2 hab hcd hsum
    rw [lift_apply g ha1 ha2, lift_apply g hb1 hb2, lift_apply g hc1 hc2,
      lift_apply g hd1 hd2] at *
    refine hg.2 ⟨a - 1, by omega⟩ ⟨b - 1, by omega⟩ ⟨c - 1, by omega⟩
      ⟨d - 1, by omega⟩ hab hcd ?_
    show (a - 1) + (b - 1) = (c - 1) + (d - 1)
    omega

/-- The box of card `i` in an "ends" placement. -/
def T (i : Fin 100) : ZMod 3 := if (i : ℕ) = 0 then 0 else if (i : ℕ) = 99 then 1 else 2

lemma T_of_zero (i : Fin 100) (h : (i : ℕ) = 0) : T i = 0 := by
  unfold T; rw [if_pos h]

lemma T_of_99 (i : Fin 100) (h : (i : ℕ) = 99) : T i = 1 := by
  unfold T; rw [if_neg (by omega), if_pos h]

lemma T_of_other (i : Fin 100) (h0 : (i : ℕ) ≠ 0) (h99 : (i : ℕ) ≠ 99) : T i = 2 := by
  unfold T; rw [if_neg h0, if_neg h99]

lemma eq_zero_of_T {i : Fin 100} (h : T i = 0) : (i : ℕ) = 0 := by
  by_contra h0
  by_cases h99 : (i : ℕ) = 99
  · rw [T_of_99 i h99] at h; exact absurd h (by decide)
  · rw [T_of_other i h0 h99] at h; exact absurd h (by decide)

lemma eq_99_of_T {i : Fin 100} (h : T i = 1) : (i : ℕ) = 99 := by
  by_contra h99
  by_cases h0 : (i : ℕ) = 0
  · rw [T_of_zero i h0] at h; exact absurd h (by decide)
  · rw [T_of_other i h0 h99] at h; exact absurd h (by decide)

lemma ne_of_T2 {i : Fin 100} (h : T i = 2) : (i : ℕ) ≠ 0 ∧ (i : ℕ) ≠ 99 := by
  constructor
  · intro h0; rw [T_of_zero i h0] at h; exact absurd h (by decide)
  · intro h99; rw [T_of_99 i h99] at h; exact absurd h (by decide)

/-- The mod-3 placements of the 100 cards. -/
def mod3fun (σ : Equiv.Perm (ZMod 3)) : Fin 100 → ZMod 3 :=
  fun i ↦ σ (Nat.cast ((i : ℕ) + 1))

lemma mod3fun_apply0 (σ : Equiv.Perm (ZMod 3)) : mod3fun σ 0 = σ 1 := by
  show σ (Nat.cast (((0 : Fin 100) : ℕ) + 1)) = σ 1
  rw [show ((0 : Fin 100) : ℕ) + 1 = 1 from rfl, Nat.cast_one]

lemma mod3fun_apply1 (σ : Equiv.Perm (ZMod 3)) : mod3fun σ 1 = σ 2 := by
  show σ (Nat.cast (((1 : Fin 100) : ℕ) + 1)) = σ 2
  rw [show ((1 : Fin 100) : ℕ) + 1 = 2 from rfl, Nat.cast_ofNat]

lemma mod3fun_apply2 (σ : Equiv.Perm (ZMod 3)) : mod3fun σ 2 = σ 0 := by
  show σ (Nat.cast (((2 : Fin 100) : ℕ) + 1)) = σ 0
  rw [show ((2 : Fin 100) : ℕ) + 1 = 3 from rfl, ZMod.natCast_self]

/-- The "ends" placements of the 100 cards. -/
def endsfun (σ : Equiv.Perm (ZMod 3)) : Fin 100 → ZMod 3 := fun i ↦ σ (T i)

lemma endsfun_apply0 (σ : Equiv.Perm (ZMod 3)) : endsfun σ 0 = σ 0 := by
  show σ (T 0) = σ 0; rw [T_of_zero 0 rfl]

lemma endsfun_apply1 (σ : Equiv.Perm (ZMod 3)) : endsfun σ 1 = σ 2 := by
  show σ (T 1) = σ 2; rw [T_of_other 1 (by decide) (by decide)]

lemma endsfun_apply2 (σ : Equiv.Perm (ZMod 3)) : endsfun σ 2 = σ 2 := by
  show σ (T 2) = σ 2; rw [T_of_other 2 (by decide) (by decide)]

lemma endsfun_apply99 (σ : Equiv.Perm (ZMod 3)) : endsfun σ 99 = σ 1 := by
  show σ (T 99) = σ 1; rw [T_of_99 99 rfl]

lemma mod3fun_valid (σ : Equiv.Perm (ZMod 3)) : GoodPlacement (mod3fun σ) := by
  constructor
  · intro b
    obtain ⟨r, hr⟩ := σ.surjective b
    rcases tri r with rfl | rfl | rfl
    · exact ⟨2, by rw [mod3fun_apply2]; exact hr⟩
    · exact ⟨0, by rw [mod3fun_apply0]; exact hr⟩
    · exact ⟨1, by rw [mod3fun_apply1]; exact hr⟩
  · intro i j k l hij hkl hsum
    have hij' : (Nat.cast ((i : ℕ) + 1) : ZMod 3) ≠ Nat.cast ((j : ℕ) + 1) :=
      σ.injective.ne_iff.mp hij
    have hkl' : (Nat.cast ((k : ℕ) + 1) : ZMod 3) ≠ Nat.cast ((l : ℕ) + 1) :=
      σ.injective.ne_iff.mp hkl
    have hcast : (Nat.cast ((i : ℕ) + 1) : ZMod 3) + Nat.cast ((j : ℕ) + 1) =
        Nat.cast ((k : ℕ) + 1) + Nat.cast ((l : ℕ) + 1) := by
      have h2 : ((i : ℕ) + 1) + ((j : ℕ) + 1) = ((k : ℕ) + 1) + ((l : ℕ) + 1) := by
        omega
      rw [← Nat.cast_add, ← Nat.cast_add, h2, Nat.cast_add]
    rcases pair_eq_of_sum hij' hkl' hcast with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨congrArg σ h1, congrArg σ h2⟩
    · exact Or.inr ⟨congrArg σ h1, congrArg σ h2⟩

/-- For a pair of indices from two different `T`-boxes, the sum determines
the (unordered) pair of `T`-values. -/
lemma bucket_of_ne {i j : Fin 100} (hij : T i ≠ T j) :
    (((T i = 0 ∧ T j = 1) ∨ (T i = 1 ∧ T j = 0)) ∧ (i : ℕ) + j = 99) ∨
    (((T i = 0 ∧ T j = 2) ∨ (T i = 2 ∧ T j = 0)) ∧ (i : ℕ) + j < 99) ∨
    (((T i = 1 ∧ T j = 2) ∨ (T i = 2 ∧ T j = 1)) ∧ 99 < (i : ℕ) + j) := by
  obtain h0 | h1 | h2 := tri (T i) <;> obtain k0 | k1 | k2 := tri (T j)
  · exact absurd (h0.trans k0.symm) hij
  · refine Or.inl ⟨Or.inl ⟨h0, k1⟩, ?_⟩
    have hi := eq_zero_of_T h0; have hj := eq_99_of_T k1; omega
  · refine Or.inr <| Or.inl ⟨Or.inl ⟨h0, k2⟩, ?_⟩
    have hi := eq_zero_of_T h0; obtain ⟨hj1, hj2⟩ := ne_of_T2 k2; omega
  · refine Or.inl ⟨Or.inr ⟨h1, k0⟩, ?_⟩
    have hi := eq_99_of_T h1; have hj := eq_zero_of_T k0; omega
  · exact absurd (h1.trans k1.symm) hij
  · refine Or.inr <| Or.inr ⟨Or.inl ⟨h1, k2⟩, ?_⟩
    have hi := eq_99_of_T h1; obtain ⟨hj1, hj2⟩ := ne_of_T2 k2; omega
  · refine Or.inr <| Or.inl ⟨Or.inr ⟨h2, k0⟩, ?_⟩
    obtain ⟨hi1, hi2⟩ := ne_of_T2 h2; have hj := eq_zero_of_T k0; omega
  · refine Or.inr <| Or.inr ⟨Or.inr ⟨h2, k1⟩, ?_⟩
    obtain ⟨hi1, hi2⟩ := ne_of_T2 h2; have hj := eq_99_of_T k1; omega
  · exact absurd (h2.trans k2.symm) hij

lemma ends_pair {i j k l : Fin 100} (hij : T i ≠ T j) (hkl : T k ≠ T l)
    (h : (i : ℕ) + j = (k : ℕ) + l) :
    (T i = T k ∧ T j = T l) ∨ (T i = T l ∧ T j = T k) := by
  obtain ⟨hp, hs⟩ | ⟨hp, hs⟩ | ⟨hp, hs⟩ := bucket_of_ne hij <;>
  obtain ⟨hq, ht⟩ | ⟨hq, ht⟩ | ⟨hq, ht⟩ := bucket_of_ne hkl <;>
  first
    | (exfalso; omega)
    | (rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
       rcases hq with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> simp_all)

lemma endsfun_valid (σ : Equiv.Perm (ZMod 3)) : GoodPlacement (endsfun σ) := by
  constructor
  · intro b
    obtain ⟨r, hr⟩ := σ.surjective b
    rcases tri r with rfl | rfl | rfl
    · exact ⟨0, by rw [endsfun_apply0]; exact hr⟩
    · exact ⟨99, by rw [endsfun_apply99]; exact hr⟩
    · exact ⟨1, by rw [endsfun_apply1]; exact hr⟩
  · intro i j k l hij hkl hsum
    have hij' : T i ≠ T j := σ.injective.ne_iff.mp hij
    have hkl' : T k ≠ T l := σ.injective.ne_iff.mp hkl
    rcases ends_pair hij' hkl' hsum with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨congrArg σ h1, congrArg σ h2⟩
    · exact Or.inr ⟨congrArg σ h1, congrArg σ h2⟩

/-- Every valid placement is one of the twelve explicit placements. -/
lemma mem_solutions {g : Fin 100 → ZMod 3} (hg : GoodPlacement g) :
    g ∈ Set.range mod3fun ∪ Set.range endsfun := by
  rcases classify 100 (by norm_num) (lift g) (lift_good hg) with hmod | hends
  · obtain ⟨σ, hσ⟩ := hmod
    refine Or.inl ⟨σ, funext fun i ↦ ?_⟩
    have h1 : 1 ≤ (i : ℕ) + 1 := by omega
    have h2b : (i : ℕ) + 1 ≤ 100 := by omega
    have this := hσ (↑i + 1) h1 h2b
    rw [lift_apply_fin] at this
    exact this.symm
  · obtain ⟨σ, h0, h1, h2⟩ := hends
    refine Or.inr ⟨σ, funext fun i ↦ ?_⟩
    by_cases hi0 : (i : ℕ) = 0
    · have hTi : T i = 0 := T_of_zero i hi0
      have hg0 : g i = σ 0 := by
        rw [← lift_apply_fin g i]
        have h10 : (i : ℕ) + 1 = 1 := by omega
        rw [h10]; exact h0
      rw [hg0]; show σ (T i) = σ 0; rw [hTi]
    · by_cases hi99 : (i : ℕ) = 99
      · have hTi : T i = 1 := T_of_99 i hi99
        have hg1 : g i = σ 1 := by
          rw [← lift_apply_fin g i]
          have h100 : (i : ℕ) + 1 = 100 := by omega
          rw [h100]; exact h1
        rw [hg1]; show σ (T i) = σ 1; rw [hTi]
      · have hTi : T i = 2 := T_of_other i hi0 hi99
        have hg2 : g i = σ 2 := by
          rw [← lift_apply_fin g i]
          exact h2 (↑i + 1) (by omega) (by omega)
        rw [hg2]; show σ (T i) = σ 2; rw [hTi]

lemma mod3fun_injective : Function.Injective mod3fun := by
  intro σ τ h
  ext r
  rcases tri r with rfl | rfl | rfl
  · have h2 := congrFun h 2
    rw [mod3fun_apply2, mod3fun_apply2] at h2
    exact h2
  · have h0 := congrFun h 0
    rw [mod3fun_apply0, mod3fun_apply0] at h0
    exact h0
  · have h1 := congrFun h 1
    rw [mod3fun_apply1, mod3fun_apply1] at h1
    exact h1

lemma endsfun_injective : Function.Injective endsfun := by
  intro σ τ h
  ext r
  rcases tri r with rfl | rfl | rfl
  · have h0 := congrFun h 0
    rw [endsfun_apply0, endsfun_apply0] at h0
    exact h0
  · have h99 := congrFun h 99
    rw [endsfun_apply99, endsfun_apply99] at h99
    exact h99
  · have h1 := congrFun h 1
    rw [endsfun_apply1, endsfun_apply1] at h1
    exact h1

lemma disjoint_ranges : Disjoint (Set.range mod3fun) (Set.range endsfun) := by
  rw [Set.disjoint_iff]
  rintro g ⟨⟨σ, hσ⟩, ⟨τ, hτ⟩⟩
  have h1 := congrFun hσ 1
  rw [← hτ, mod3fun_apply1, endsfun_apply1] at h1
  have h2 := congrFun hσ 2
  rw [← hτ, mod3fun_apply2, endsfun_apply2] at h2
  have h20 : σ 2 = σ 0 := h1.trans h2.symm
  have hcon := σ.injective h20
  exact absurd hcon (by decide)

lemma card_perm_zmod3 : Fintype.card (Equiv.Perm (ZMod 3)) = 6 := by
  have h : Nat.factorial 3 = 6 := rfl
  rw [Fintype.card_perm, ZMod.card, h]

lemma card_mod3fun_range : (Set.range mod3fun).ncard = 6 := by
  rw [← Set.image_univ, Set.ncard_image_of_injective Set.univ mod3fun_injective,
    Set.ncard_univ, Nat.card_eq_fintype_card, card_perm_zmod3]

lemma card_endsfun_range : (Set.range endsfun).ncard = 6 := by
  rw [← Set.image_univ, Set.ncard_image_of_injective Set.univ endsfun_injective,
    Set.ncard_univ, Nat.card_eq_fintype_card, card_perm_zmod3]

lemma card_solutions : {g : Fin 100 → ZMod 3 | GoodPlacement g}.ncard = 12 := by
  have h12 : 6 + 6 = 12 := rfl
  have hset : {g : Fin 100 → ZMod 3 | GoodPlacement g} =
      Set.range mod3fun ∪ Set.range endsfun := by
    ext g
    constructor
    · intro hg
      exact mem_solutions hg
    · rintro (⟨σ, rfl⟩ | ⟨σ, rfl⟩)
      · exact mod3fun_valid σ
      · exact endsfun_valid σ
  rw [hset, Set.ncard_union_eq disjoint_ranges (Set.toFinite _) (Set.toFinite _),
    card_mod3fun_range, card_endsfun_range, h12]

/-- The valid placements are exactly the good placements, so there are
twelve of them. -/
lemma card_valid : {g : Fin 100 → ZMod 3 | ValidPlacement g}.ncard = 12 := by
  have hset : {g : Fin 100 → ZMod 3 | ValidPlacement g} =
      {g : Fin 100 → ZMod 3 | GoodPlacement g} :=
    Set.ext fun g ↦ valid_iff_good g
  rw [hset]
  exact card_solutions

snip end

determine solution_value : ℕ := 12

problem imo2000_p4 :
    {g : Fin 100 → ZMod 3 | ValidPlacement g}.ncard = solution_value := by
  exact card_valid

end Imo2000P4
