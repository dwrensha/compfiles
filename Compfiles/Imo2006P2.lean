/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Tactic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics, .Geometry] }

/-!
# International Mathematical Olympiad 2006, Problem 2

Let $P$ be a regular 2006-gon. A diagonal is called *good* if its endpoints divide
the boundary of $P$ into two parts, each composed of an odd number of sides of $P$.
The sides of $P$ are also called *good*. Suppose $P$ has been dissected into triangles
by 2003 diagonals, no two of which have a common point in the interior of $P$.
Find the maximum number of isosceles triangles having two good sides that could appear
in such a configuration.

## Formalization notes

We model the vertices of the regular 2006-gon as `ZMod 2006`; `arc a b` is the number
of boundary edges on the counterclockwise arc from `a` to `b`. A chord is *good* iff its
arc length is odd. In a regular polygon inscribed in a circle, the length of a chord is
determined by the number of boundary edges it spans, so we express "isosceles" as the
equality of the corresponding `minArc`s. A dissection is modeled as a finset of
3-element vertex sets satisfying the combinatorial properties of a triangulation
(each polygon side belongs to exactly one triangle, each diagonal to exactly two,
the diagonals are pairwise non-crossing, there are 2004 triangles and 2003 diagonals).
-/

namespace Imo2006P2

open Finset

instance : NeZero (2006 : ℕ) := ⟨by norm_num⟩

/-- The number of sides of the 2006-gon on the counterclockwise arc from `a` to `b`. -/
def arc (a b : ZMod 2006) : ℕ := (b - a).val

/-- `b` lies strictly between `a` and `c` on the counterclockwise arc from `a` to `c`. -/
abbrev Btw (a b c : ZMod 2006) : Prop := 0 < arc a b ∧ arc a b < arc a c

instance (a b c : ZMod 2006) : Decidable (Btw a b c) :=
  inferInstanceAs (Decidable (0 < arc a b ∧ arc a b < arc a c))

/-- The length (in boundary edges) of the shorter of the two arcs between `a` and `b`. -/
def minArc (a b : ZMod 2006) : ℕ := min (arc a b) (arc b a)

/-- A pair of vertices is a *diagonal* of the polygon (i.e. not a side). -/
abbrev IsDiag (p : Finset (ZMod 2006)) : Prop :=
  ∃ a ∈ p, ∃ b ∈ p, a ≠ b ∧ arc a b ≠ 1 ∧ arc a b ≠ 2005

instance : DecidablePred IsDiag := fun p =>
  inferInstanceAs (Decidable (∃ a ∈ p, ∃ b ∈ p, a ≠ b ∧ arc a b ≠ 1 ∧ arc a b ≠ 2005))

/-- A pair of vertices is *good* if it spans an odd number of boundary sides. -/
abbrev IsGoodPair (p : Finset (ZMod 2006)) : Prop :=
  ∃ a ∈ p, ∃ b ∈ p, a ≠ b ∧ arc a b % 2 = 1

instance : DecidablePred IsGoodPair := fun p =>
  inferInstanceAs (Decidable (∃ a ∈ p, ∃ b ∈ p, a ≠ b ∧ arc a b % 2 = 1))

/-- Two chords *cross*, i.e. have a common interior point. -/
abbrev Cross (p q : Finset (ZMod 2006)) : Prop :=
  ∃ a ∈ p, ∃ b ∈ p, ∃ c ∈ q, ∃ d ∈ q,
    (Btw a c b ∧ Btw b d a) ∨ (Btw a d b ∧ Btw b c a)

instance : DecidableRel Cross := fun p q =>
  inferInstanceAs (Decidable (∃ a ∈ p, ∃ b ∈ p, ∃ c ∈ q, ∃ d ∈ q,
    (Btw a c b ∧ Btw b d a) ∨ (Btw a d b ∧ Btw b c a)))

/-- A triangle is *isosceles*: two of its sides span the same number of boundary edges. -/
abbrev Isosceles (T : Finset (ZMod 2006)) : Prop :=
  ∃ a ∈ T, ∃ b ∈ T, ∃ c ∈ T, ∃ d ∈ T, a ≠ b ∧ c ≠ d ∧
    ({a, b} : Finset (ZMod 2006)) ≠ {c, d} ∧ minArc a b = minArc c d

instance : DecidablePred Isosceles := fun T =>
  inferInstanceAs (Decidable (∃ a ∈ T, ∃ b ∈ T, ∃ c ∈ T, ∃ d ∈ T, a ≠ b ∧ c ≠ d ∧
    ({a, b} : Finset (ZMod 2006)) ≠ {c, d} ∧ minArc a b = minArc c d))

/-- The number of good sides of a triangle. -/
def ng (T : Finset (ZMod 2006)) : ℕ := ((T.powersetCard 2).filter IsGoodPair).card

/-- A triangle is *special* if it is isosceles and has two good sides. -/
abbrev IsSpecial (T : Finset (ZMod 2006)) : Prop := Isosceles T ∧ 2 ≤ ng T

instance : DecidablePred IsSpecial := fun T => inferInstanceAs (Decidable (Isosceles T ∧ 2 ≤ ng T))

/-- The diagonals used by a family of triangles. -/
def diags (D : Finset (Finset (ZMod 2006))) : Finset (Finset (ZMod 2006)) :=
  D.biUnion fun T => (T.powersetCard 2).filter IsDiag

/-- The good diagonals used by a family of triangles. -/
def goodDiags (D : Finset (Finset (ZMod 2006))) : Finset (Finset (ZMod 2006)) :=
  (diags D).filter IsGoodPair

/-- Predicate that a set of chords is pairwise non-crossing, phrased as a function of
the set of chords so that `diags D` is evaluated only once during decidable evaluation. -/
def noncrossPred (ds : Finset (Finset (ZMod 2006))) : Prop :=
  ∀ p ∈ ds, ∀ q ∈ ds, ¬Cross p q

instance : DecidablePred noncrossPred := fun ds =>
  inferInstanceAs (Decidable (∀ p ∈ ds, ∀ q ∈ ds, ¬Cross p q))

/-- A dissection of the 2006-gon into triangles by 2003 non-crossing diagonals,
modeled combinatorially as a family of 3-element vertex sets. -/
def IsDissection (D : Finset (Finset (ZMod 2006))) : Prop :=
  (∀ T ∈ D, T.card = 3) ∧
  D.card = 2004 ∧
  (∀ i : ZMod 2006, (D.filter fun T => ({i, i + 1} : Finset (ZMod 2006)) ⊆ T).card = 1) ∧
  (∀ T ∈ D, ∀ p ∈ T.powersetCard 2, IsDiag p → (D.filter fun T' => p ⊆ T').card = 2) ∧
  noncrossPred (diags D) ∧
  (diags D).card = 2003

instance {D : Finset (Finset (ZMod 2006))} : Decidable (IsDissection D) :=
  inferInstanceAs (Decidable
    ((∀ T ∈ D, T.card = 3) ∧
     D.card = 2004 ∧
     (∀ i : ZMod 2006, (D.filter fun T => ({i, i + 1} : Finset (ZMod 2006)) ⊆ T).card = 1) ∧
     (∀ T ∈ D, ∀ p ∈ T.powersetCard 2, IsDiag p → (D.filter fun T' => p ⊆ T').card = 2) ∧
     noncrossPred (diags D) ∧
     (diags D).card = 2003))

snip begin

/-!
## Sketch of solution

The answer is $1003$. For the upper bound (following the official graph-theoretic
solution, cf. Evan Chen's notes): every triangle of the dissection has an even number
of good sides (parity), so a triangle has either $0$ or $2$ good sides. Double-counting
incidences between triangles and good pairs of vertices (each good diagonal lies in
exactly two triangles, each of the 2006 polygon sides in exactly one) gives
$2L = 2k + 2006$, where $L$ is the number of triangles with two good sides and $k$ the
number of good diagonals; hence $L = 1003 + k$. On the other hand every good diagonal
$AB$ has, on the side of its shorter arc, an adjacent triangle $ABV$; that triangle has
two good sides but is *not* isosceles, and this assignment is injective. Hence at least
$k$ of the $L$ triangles are not isosceles, so at most $L - k = 1003$ triangles are
isosceles with two good sides. The bound is attained by cutting off the $1003$ ears
$\{2i, 2i+1, 2i+2\}$ and triangulating the remaining central $1003$-gon by a fan.
-/

section arc_api

lemma noncrossPred_iff {ds : Finset (Finset (ZMod 2006))} :
    noncrossPred ds ↔ ∀ p ∈ ds, ∀ q ∈ ds, ¬Cross p q := Iff.rfl

lemma arc_self (a : ZMod 2006) : arc a a = 0 := by simp [arc]

lemma arc_eq_zero {a b : ZMod 2006} : arc a b = 0 ↔ a = b := by
  show (b - a).val = 0 ↔ a = b
  rw [ZMod.val_eq_zero, sub_eq_zero]
  exact eq_comm

lemma arc_pos {a b : ZMod 2006} (h : a ≠ b) : 0 < arc a b := by
  rw [Nat.pos_iff_ne_zero, ne_eq, arc_eq_zero]; exact h

lemma arc_lt (a b : ZMod 2006) : arc a b < 2006 := ZMod.val_lt _

lemma arc_add_arc {a b : ZMod 2006} (h : a ≠ b) : arc a b + arc b a = 2006 := by
  have h1 : ((b - a) + (a - b) : ZMod 2006) = 0 := by abel
  have h2 : (((b - a) + (a - b) : ZMod 2006)).val = (arc a b + arc b a) % 2006 :=
    ZMod.val_add _ _
  rw [h1, ZMod.val_zero] at h2
  have h3 := arc_pos h; have h4 := arc_pos (Ne.symm h)
  have h5 := arc_lt a b; have h6 := arc_lt b a
  omega

lemma arc_add_arc_eq (a b c : ZMod 2006) :
    arc a b + arc b c = arc a c ∨ arc a b + arc b c = arc a c + 2006 := by
  have h1 : ((b - a) + (c - b) : ZMod 2006) = c - a := by abel
  have h2 : arc a c = (arc a b + arc b c) % 2006 := by
    show (c - a).val = (arc a b + arc b c) % 2006
    rw [← h1]
    exact ZMod.val_add _ _
  have h3 := arc_lt a c
  have h4 := arc_lt a b
  have h5 := arc_lt b c
  omega

lemma arc_btw_sub {a b c : ZMod 2006} (h : Btw a b c) : arc b c = arc a c - arc a b := by
  have h1 : (c - a) - (b - a) = c - b := by abel
  have h2 := ZMod.val_sub (n := 2006) (a := c - a) (b := b - a) h.2.le
  rw [h1] at h2
  exact h2

lemma arc_eq_one {a b : ZMod 2006} (h : arc a b = 1) : b = a + 1 := by
  have h2 : (1 : ZMod 2006).val = 1 := by decide
  have h3 : b - a = 1 := ZMod.val_injective 2006 (h.trans h2.symm)
  calc b = a + (b - a) := by abel
       _ = a + 1 := by rw [h3]

lemma Btw.ne_left {a b c : ZMod 2006} (h : Btw a b c) : a ≠ b := by
  intro hh; subst hh
  have h1 := h.1
  rw [arc_self] at h1
  exact absurd h1 (lt_irrefl 0)

lemma Btw.ne_right {a b c : ZMod 2006} (h : Btw a b c) : b ≠ c := by
  intro hh; subst hh
  exact absurd h.2 (lt_irrefl _)

lemma minArc_comm (a b : ZMod 2006) : minArc a b = minArc b a := min_comm _ _

lemma minArc_le (a b : ZMod 2006) : minArc a b ≤ 1003 := by
  by_cases hab : a = b
  · simp [minArc, hab, arc_self]
  · have h := arc_add_arc hab
    have h1 := arc_lt a b; have h2 := arc_lt b a
    rcases Nat.le_total (arc a b) 1003 with h3 | h3
    · exact (min_le_left _ _).trans h3
    · exact (min_le_right _ _).trans (by omega)

lemma diagPair_iff {a b : ZMod 2006} (h : a ≠ b) :
    IsDiag {a, b} ↔ arc a b ≠ 1 ∧ arc a b ≠ 2005 := by
  constructor
  · rintro ⟨x, hx, y, hy, hxy, h1, h2⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact absurd rfl hxy
    · exact ⟨h1, h2⟩
    · have hadd := arc_add_arc h
      constructor <;> omega
    · exact absurd rfl hxy
  · rintro ⟨h1, h2⟩
    exact ⟨a, by simp, b, by simp, h, h1, h2⟩

lemma goodPair_iff {a b : ZMod 2006} (h : a ≠ b) :
    IsGoodPair {a, b} ↔ arc a b % 2 = 1 := by
  constructor
  · rintro ⟨x, hx, y, hy, hxy, h1⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact absurd rfl hxy
    · exact h1
    · have hadd := arc_add_arc h; omega
    · exact absurd rfl hxy
  · intro h1; exact ⟨a, by simp, b, by simp, h, h1⟩

lemma not_btw_iff {a v b : ZMod 2006} (hva : v ≠ a) (hvb : v ≠ b) (hab : a ≠ b) :
    ¬Btw a v b ↔ Btw b v a := by
  constructor
  · intro h
    have h1 : arc a b ≤ arc a v := by
      rcases Nat.lt_or_ge (arc a v) (arc a b) with h2 | h2
      · exact absurd ⟨arc_pos (Ne.symm hva), h2⟩ h
      · exact h2
    have h2 : arc a v ≠ arc a b := by
      intro h3
      apply hvb
      have h4 : v - a = b - a := ZMod.val_injective 2006 h3
      exact by linear_combination h4
    have h3 : arc a b < arc a v := Nat.lt_of_le_of_ne h1 (Ne.symm h2)
    have h4 := arc_add_arc_eq a v b
    have h5 := arc_add_arc hvb
    have h6 := arc_add_arc hab
    have h7 := arc_lt a v
    have h8 := arc_pos hvb
    rcases h4 with h4 | h4
    · omega
    · constructor <;> omega
  · intro h hb
    obtain ⟨hc1, hc2⟩ := h
    obtain ⟨hb1, hb2⟩ := hb
    have h1 := arc_add_arc_eq a v b
    have h2 := arc_add_arc hab
    have h3 := arc_add_arc hvb
    have h4 := arc_lt a v
    have h5 := arc_lt v b
    rcases h1 with h1 | h1 <;> omega

end arc_api

section counting

lemma pair_ne_left {a b c : ZMod 2006} (h : b ≠ c) : ({a, b} : Finset (ZMod 2006)) ≠ {a, c} := by
  intro hh
  apply h
  have h1 : b ∈ ({a, c} : Finset (ZMod 2006)) := by rw [← hh]; simp
  have h2 : c ∈ ({a, b} : Finset (ZMod 2006)) := by rw [hh]; simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
  rcases h1 with h1 | h1
  · rcases h2 with h2 | h2
    · exact h1.trans h2.symm
    · exact h2.symm
  · exact h1

lemma pair_ne_right {a b c : ZMod 2006} (h : a ≠ b) : ({a, c} : Finset (ZMod 2006)) ≠ {b, c} := by
  intro hh
  apply h
  have h1 : a ∈ ({b, c} : Finset (ZMod 2006)) := by rw [← hh]; simp
  have h2 : b ∈ ({a, c} : Finset (ZMod 2006)) := by rw [hh]; simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
  rcases h1 with h1 | h1
  · exact h1
  · rcases h2 with h2 | h2
    · exact h2.symm
    · exact h1.trans h2.symm

lemma card_three_pairs {a b c : ZMod 2006} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ({{a, b}, {a, c}, {b, c}} : Finset (Finset (ZMod 2006))).card = 3 := by
  have d1 : ({a, b} : Finset (ZMod 2006)) ≠ {a, c} := pair_ne_left hbc
  have d2 : ({b, a} : Finset (ZMod 2006)) ≠ {b, c} := pair_ne_left hac
  have d3 : ({a, c} : Finset (ZMod 2006)) ≠ {b, c} := pair_ne_right hab
  have n1 : ({a, b} : Finset (ZMod 2006)) ∉ ({{a, c}, {b, c}} : Finset (Finset (ZMod 2006))) := by
    intro hmem
    rw [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with hmem | hmem
    · exact d1 hmem
    · rw [Finset.pair_comm a b] at hmem
      exact d2 hmem
  have n2 : ({a, c} : Finset (ZMod 2006)) ∉ ({{b, c}} : Finset (Finset (ZMod 2006))) := by
    intro hmem
    rw [Finset.mem_singleton] at hmem
    exact d3 hmem
  rw [Finset.card_insert_of_notMem n1, Finset.card_insert_of_notMem n2, Finset.card_singleton]

lemma powersetCard_two_triple {a b c : ZMod 2006} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ({a, b, c} : Finset (ZMod 2006)).powersetCard 2 = {{a, b}, {a, c}, {b, c}} := by
  ext p
  simp only [Finset.mem_powersetCard, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hsub, hcard⟩
    obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hcard
    have hx : x ∈ ({a, b, c} : Finset (ZMod 2006)) := hsub (by simp)
    have hy : y ∈ ({a, b, c} : Finset (ZMod 2006)) := hsub (by simp)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
    · exact absurd rfl hxy
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl (Finset.pair_comm _ _)
    · exact absurd rfl hxy
    · exact Or.inr (Or.inr rfl)
    · exact Or.inr (Or.inl (Finset.pair_comm _ _))
    · exact Or.inr (Or.inr (Finset.pair_comm _ _))
    · exact absurd rfl hxy
  · rintro (rfl | rfl | rfl)
    · exact ⟨by intro z hz; simp at hz ⊢; tauto, Finset.card_eq_two.mpr ⟨a, b, hab, rfl⟩⟩
    · exact ⟨by intro z hz; simp at hz ⊢; tauto, Finset.card_eq_two.mpr ⟨a, c, hac, rfl⟩⟩
    · exact ⟨by intro z hz; simp at hz ⊢; tauto, Finset.card_eq_two.mpr ⟨b, c, hbc, rfl⟩⟩

lemma ng_triple {a b c : ZMod 2006} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ng {a, b, c} = (if arc a b % 2 = 1 then 1 else 0) +
      (if arc a c % 2 = 1 then 1 else 0) + (if arc b c % 2 = 1 then 1 else 0) := by
  have d1 : ({a, b} : Finset (ZMod 2006)) ≠ {a, c} := pair_ne_left hbc
  have d2 : ({a, b} : Finset (ZMod 2006)) ≠ {b, c} := by
    rw [Finset.pair_comm a b]; exact pair_ne_left hac
  have d3 : ({a, c} : Finset (ZMod 2006)) ≠ {b, c} := pair_ne_right hab
  simp only [ng, powersetCard_two_triple hab hac hbc, Finset.filter_insert,
    Finset.filter_singleton, goodPair_iff hab, goodPair_iff hac, goodPair_iff hbc]
  by_cases h1 : arc a b % 2 = 1 <;> by_cases h2 : arc a c % 2 = 1 <;>
    by_cases h3 : arc b c % 2 = 1 <;> simp [h1, h2, h3, d1, d2, d3]

lemma ng_even {a b c : ZMod 2006} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Even (ng {a, b, c}) := by
  rw [ng_triple hab hac hbc]
  have h1 := arc_add_arc_eq a b c
  by_cases h3 : arc a b % 2 = 1 <;> by_cases h4 : arc a c % 2 = 1 <;>
    by_cases h5 : arc b c % 2 = 1 <;> simp [h3, h4, h5] <;>
    rcases h1 with h1 | h1 <;> omega

lemma ng_le_three {a b c : ZMod 2006} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ng {a, b, c} ≤ 3 := by
  simp only [ng, powersetCard_two_triple hab hac hbc]
  exact (Finset.card_filter_le _ _).trans_eq (card_three_pairs hab hac hbc)

lemma one_ne_zero_zmod : (1 : ZMod 2006) ≠ 0 := by
  have h : (1 : ZMod 2006).val = 1 := by decide
  intro hh; rw [hh, ZMod.val_zero] at h; exact one_ne_zero h.symm

lemma two_ne_zero_zmod : (2 : ZMod 2006) ≠ 0 := by
  have h : (2 : ZMod 2006).val = 2 := by decide
  intro hh; rw [hh, ZMod.val_zero] at h; exact two_ne_zero h.symm

lemma side_ne (i : ZMod 2006) : i ≠ i + 1 := by
  intro h
  have h1 : (1 : ZMod 2006) = 0 := by linear_combination -h
  exact one_ne_zero_zmod h1

lemma arc_side (i : ZMod 2006) : arc i (i + 1) = 1 := by
  have e : (i + 1) - i = (1 : ZMod 2006) := by abel
  show ((i + 1) - i).val = 1
  rw [e]
  decide

lemma side_injective :
    Function.Injective (fun i : ZMod 2006 => ({i, i + 1} : Finset (ZMod 2006))) := by
  intro i j hij
  change ({i, i + 1} : Finset (ZMod 2006)) = {j, j + 1} at hij
  have h1 : i ∈ ({j, j + 1} : Finset (ZMod 2006)) := by rw [← hij]; simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1
  rcases h1 with h1 | h1
  · exact h1
  · exfalso
    have h2 : i + 1 ∈ ({j, j + 1} : Finset (ZMod 2006)) := by rw [← hij]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at h2
    rw [h1] at h2
    rcases h2 with h2 | h2
    · exact two_ne_zero_zmod (by linear_combination h2)
    · exact one_ne_zero_zmod (by linear_combination h2)

lemma card_good_sides :
    ((Finset.univ.powersetCard 2).filter fun p => IsGoodPair p ∧ ¬IsDiag p).card = 2006 := by
  have h : ((Finset.univ.powersetCard 2).filter fun p => IsGoodPair p ∧ ¬IsDiag p) =
      Finset.univ.image (fun i : ZMod 2006 => ({i, i + 1} : Finset (ZMod 2006))) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and,
      Finset.mem_image, Finset.mem_univ]
    constructor
    · rintro ⟨hp2, hgood, hnd⟩
      obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hp2
      rw [diagPair_iff hab] at hnd
      push Not at hnd
      by_cases h1 : arc a b = 1
      · exact ⟨a, by rw [arc_eq_one h1]⟩
      · have h2 := hnd h1
        have h3 := arc_add_arc hab
        have h4 : arc b a = 1 := by omega
        exact ⟨b, by rw [arc_eq_one h4]; exact Finset.pair_comm _ _⟩
    · rintro ⟨i, rfl⟩
      have hne := side_ne i
      have harc := arc_side i
      refine ⟨Finset.card_eq_two.mpr ⟨i, i + 1, hne, rfl⟩, ?_, ?_⟩
      · rw [goodPair_iff hne, harc]
      · intro hdiag
        rw [diagPair_iff hne] at hdiag
        exact hdiag.1 harc
  rw [h, Finset.card_image_of_injective _ side_injective, Finset.card_univ, ZMod.card]

lemma count_containing {D : Finset (Finset (ZMod 2006))} (hD : IsDissection D)
    {p : Finset (ZMod 2006)} (hp2 : p.card = 2) (hgood : IsGoodPair p) :
    (D.filter fun T => p ⊆ T).card = if IsDiag p then (if p ∈ diags D then 2 else 0) else 1 := by
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hp2
  by_cases hd : IsDiag {a, b}
  · rw [if_pos hd]
    by_cases hdr : ({a, b} : Finset (ZMod 2006)) ∈ diags D
    · rw [if_pos hdr]
      simp only [diags, Finset.mem_biUnion] at hdr
      obtain ⟨T₀, hT₀, hpT₀⟩ := hdr
      rw [Finset.mem_filter, Finset.mem_powersetCard] at hpT₀
      exact hD.2.2.2.1 T₀ hT₀ {a, b}
        (Finset.mem_powersetCard.mpr ⟨hpT₀.1.1, hpT₀.1.2⟩) hpT₀.2
    · rw [if_neg hdr]
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro T hT hsub
      apply hdr
      simp only [diags, Finset.mem_biUnion]
      exact ⟨T, hT, Finset.mem_filter.mpr
        ⟨Finset.mem_powersetCard.mpr ⟨hsub, Finset.card_eq_two.mpr ⟨a, b, hab, rfl⟩⟩, hd⟩⟩
  · rw [if_neg hd]
    rw [diagPair_iff hab] at hd
    push Not at hd
    by_cases h1 : arc a b = 1
    · rw [arc_eq_one h1]
      exact hD.2.2.1 a
    · have h2 := hd h1
      have h3 := arc_add_arc hab
      have h4 : arc b a = 1 := by omega
      have h5 : ({a, b} : Finset (ZMod 2006)) = {b, b + 1} := by
        rw [arc_eq_one h4]; exact Finset.pair_comm _ _
      rw [h5]
      exact hD.2.2.1 b

lemma sum_ng_eq {D : Finset (Finset (ZMod 2006))} (hD : IsDissection D) :
    ∑ T ∈ D, ng T = 2 * (goodDiags D).card + 2006 := by
  classical
  set P : Finset (Finset (ZMod 2006)) := Finset.univ.powersetCard 2 with hP
  have hmemP : ∀ {p : Finset (ZMod 2006)}, p ∈ P ↔ p.card = 2 := by
    intro p
    simp [hP, Finset.mem_powersetCard]
  have step1 : ∑ T ∈ D, ng T =
      ∑ T ∈ D, (P.bipartiteAbove (fun T p => p ⊆ T ∧ IsGoodPair p) T).card := by
    apply Finset.sum_congr rfl
    intro T hT
    simp only [ng]
    congr 1
    ext p
    simp only [Finset.mem_bipartiteAbove, hmemP, Finset.mem_filter, Finset.mem_powersetCard]
    tauto
  rw [step1, Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow]
  have hb : ∀ p ∈ P, (D.bipartiteBelow (fun T p => p ⊆ T ∧ IsGoodPair p) p).card =
      (D.filter fun T => p ⊆ T ∧ IsGoodPair p).card := fun p _ => rfl
  rw [Finset.sum_congr rfl hb]
  rw [← Finset.sum_filter_add_sum_filter_not P IsGoodPair]
  have hz : ∑ p ∈ P.filter (¬ IsGoodPair ·), (D.filter fun T => p ⊆ T ∧ IsGoodPair p).card = 0 := by
    apply Finset.sum_eq_zero
    intro p hp
    rw [Finset.mem_filter] at hp
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro T hT
    exact fun h => hp.2 h.2
  rw [hz, add_zero]
  have hg : ∀ p ∈ P.filter IsGoodPair, (D.filter fun T => p ⊆ T ∧ IsGoodPair p).card =
      (D.filter fun T => p ⊆ T).card := by
    intro p hp
    rw [Finset.mem_filter] at hp
    have hfilter : D.filter (fun T => p ⊆ T ∧ IsGoodPair p) = D.filter (fun T => p ⊆ T) := by
      ext T
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hT, h1, -⟩
        exact ⟨hT, h1⟩
      · rintro ⟨hT, h1⟩
        exact ⟨hT, h1, hp.2⟩
    rw [hfilter]
  rw [Finset.sum_congr rfl hg]
  rw [← Finset.sum_filter_add_sum_filter_not (P.filter IsGoodPair) IsDiag]
  have hd : ∑ p ∈ (P.filter IsGoodPair).filter IsDiag, (D.filter fun T => p ⊆ T).card =
      2 * (goodDiags D).card := by
    have h1 : ∀ p ∈ (P.filter IsGoodPair).filter IsDiag, (D.filter fun T => p ⊆ T).card =
        (if p ∈ diags D then 2 else 0) := by
      intro p hp
      rw [Finset.mem_filter, Finset.mem_filter] at hp
      have hcc := count_containing hD (hmemP.mp hp.1.1) hp.1.2
      rw [if_pos hp.2] at hcc
      exact hcc
    rw [Finset.sum_congr rfl h1, ← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
    have hdbl : ((P.filter IsGoodPair).filter IsDiag).filter (· ∈ diags D) = goodDiags D := by
      ext p
      simp only [Finset.mem_filter, goodDiags]
      constructor
      · rintro ⟨⟨⟨hpP, hgood⟩, hdiag⟩, hdr⟩
        exact ⟨hdr, hgood⟩
      · rintro ⟨hdr, hgood⟩
        have hdiag : IsDiag p := by
          simp only [diags, Finset.mem_biUnion] at hdr
          obtain ⟨T, hT, hpT⟩ := hdr
          exact (Finset.mem_filter.mp hpT).2
        have hpP : p ∈ P := by
          rw [hmemP]
          simp only [diags, Finset.mem_biUnion] at hdr
          obtain ⟨T, hT, hpT⟩ := hdr
          exact (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hpT).1).2
        exact ⟨⟨⟨hpP, hgood⟩, hdiag⟩, hdr⟩
    rw [hdbl, mul_comm]
  rw [hd]
  have hs : ∑ p ∈ (P.filter IsGoodPair).filter (¬ IsDiag ·), (D.filter fun T => p ⊆ T).card =
      2006 := by
    have h1 : ∀ p ∈ (P.filter IsGoodPair).filter (¬ IsDiag ·),
        (D.filter fun T => p ⊆ T).card = 1 := by
      intro p hp
      rw [Finset.mem_filter, Finset.mem_filter] at hp
      have hcc := count_containing hD (hmemP.mp hp.1.1) hp.1.2
      rw [if_neg hp.2] at hcc
      exact hcc
    rw [Finset.sum_congr rfl h1, Finset.sum_const, smul_eq_mul, mul_one, Finset.filter_filter]
    exact card_good_sides
  rw [hs]

lemma card_goodish {D : Finset (Finset (ZMod 2006))} (hD : IsDissection D) :
    (D.filter fun T => ng T = 2).card = (goodDiags D).card + 1003 := by
  have hsum := sum_ng_eq hD
  have hpar : ∀ T ∈ D, ng T = 0 ∨ ng T = 2 := by
    intro T hT
    have hT3 := hD.1 T hT
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hT3
    have hev := ng_even hab hac hbc
    have hle := ng_le_three hab hac hbc
    rcases hev with ⟨k, hk⟩
    omega
  have hsum2 : ∑ T ∈ D, ng T = 2 * (D.filter fun T => ng T = 2).card := by
    have h : ∀ T ∈ D, ng T = (if ng T = 2 then 2 else 0) := by
      intro T hT
      rcases hpar T hT with h0 | h2
      · simp [h0]
      · simp [h2]
    rw [Finset.sum_congr rfl h, ← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_comm]
  omega

end counting

section charging

/-- `v` lies on the shorter of the two arcs cut out by the chord `d`. -/
abbrev OnShortArc (d : Finset (ZMod 2006)) (v : ZMod 2006) : Prop :=
  ∀ a ∈ d, ∀ b ∈ d, a ≠ b →
    arc a v + arc v b = min (arc a b) (arc b a) ∨ arc b v + arc v a = min (arc a b) (arc b a)

/-- The triangle charged to a good diagonal `d`: adjacent to `d` on its short-arc side,
with two good sides but not isosceles. -/
abbrev IsShortTri (D : Finset (Finset (ZMod 2006))) (d T : Finset (ZMod 2006)) : Prop :=
  T ∈ D ∧ d ⊆ T ∧ (∀ v ∈ T \ d, OnShortArc d v) ∧ ng T = 2 ∧ ¬Isosceles T

lemma isosceles_triple {a b c : ZMod 2006} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Isosceles {a, b, c} ↔
      minArc a b = minArc a c ∨ minArc a b = minArc b c ∨ minArc a c = minArc b c := by
  have key : ∀ {x y p q : ZMod 2006}, x ≠ y → ({x, y} : Finset (ZMod 2006)) = {p, q} →
      minArc x y = minArc p q := by
    intro x y p q hxy h
    have hx : x ∈ ({p, q} : Finset (ZMod 2006)) := by rw [← h]; simp
    have hy : y ∈ ({p, q} : Finset (ZMod 2006)) := by rw [← h]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact absurd rfl hxy
    · rfl
    · exact minArc_comm _ _
    · exact absurd rfl hxy
  constructor
  · rintro ⟨x, hx, y, hy, z, hz, w, hw, hxy, hzw, hne, heq⟩
    have hsub1 : ({x, y} : Finset (ZMod 2006)) ∈ ({a, b, c} : Finset _).powersetCard 2 := by
      rw [Finset.mem_powersetCard]
      refine ⟨?_, Finset.card_eq_two.mpr ⟨x, y, hxy, rfl⟩⟩
      intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl
      · exact hx
      · exact hy
    have hsub2 : ({z, w} : Finset (ZMod 2006)) ∈ ({a, b, c} : Finset _).powersetCard 2 := by
      rw [Finset.mem_powersetCard]
      refine ⟨?_, Finset.card_eq_two.mpr ⟨z, w, hzw, rfl⟩⟩
      intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl
      · exact hz
      · exact hw
    rw [powersetCard_two_triple hab hac hbc] at hsub1 hsub2
    simp only [Finset.mem_insert, Finset.mem_singleton] at hsub1 hsub2
    rcases hsub1 with h1 | h1 | h1 <;> rcases hsub2 with h2 | h2 | h2
    · exact absurd (h1.trans h2.symm) hne
    · left; rw [key hxy h1, key hzw h2] at heq; exact heq
    · right; left; rw [key hxy h1, key hzw h2] at heq; exact heq
    · left; rw [key hxy h1, key hzw h2] at heq; exact heq.symm
    · exact absurd (h1.trans h2.symm) hne
    · right; right; rw [key hxy h1, key hzw h2] at heq; exact heq
    · right; left; rw [key hxy h1, key hzw h2] at heq; exact heq.symm
    · right; right; rw [key hxy h1, key hzw h2] at heq; exact heq.symm
    · exact absurd (h1.trans h2.symm) hne
  · have d1 : ({a, b} : Finset (ZMod 2006)) ≠ {a, c} := pair_ne_left hbc
    have d2 : ({a, b} : Finset (ZMod 2006)) ≠ {b, c} := by
      rw [Finset.pair_comm a b]; exact pair_ne_left hac
    have d3 : ({a, c} : Finset (ZMod 2006)) ≠ {b, c} := pair_ne_right hab
    rintro (h | h | h)
    · exact ⟨a, by simp, b, by simp, a, by simp, c, by simp, hab, hac, d1, h⟩
    · exact ⟨a, by simp, b, by simp, b, by simp, c, by simp, hab, hbc, d2, h⟩
    · exact ⟨a, by simp, c, by simp, b, by simp, c, by simp, hac, hbc, d3, h⟩

lemma cross_contra {D : Finset (Finset (ZMod 2006))} (hD : IsDissection D)
    {A B v₁ v₂ : ZMod 2006} {T₁ T₂ : Finset (ZMod 2006)}
    (hT₁ : T₁ ∈ D) (hT₂ : T₂ ∈ D)
    (hT₁eq : T₁ = {v₁, A, B}) (hT₂eq : T₂ = {v₂, A, B})
    (h1 : Btw A v₁ B) (h2 : Btw A v₂ B) (hlt : arc A v₁ < arc A v₂) : False := by
  have hAB : A ≠ B := by
    intro hh; subst hh; exact absurd h1.2 (by simp [arc_self])
  have hv₁B : v₁ ≠ B := h1.ne_right
  have hv₂B : v₂ ≠ B := h2.ne_right
  have hv₁A : v₁ ≠ A := Ne.symm h1.ne_left
  have hv₂A : v₂ ≠ A := Ne.symm h2.ne_left
  have e1 := arc_btw_sub h1
  have e2 := arc_btw_sub h2
  have e3 : arc v₁ v₂ = arc A v₂ - arc A v₁ := arc_btw_sub ⟨h1.1, hlt⟩
  have hb1 := h1.1; have hb2 := h1.2; have hb3 := h2.1; have hb4 := h2.2
  have hadd := arc_add_arc hAB
  have hadd1 := arc_add_arc hv₁B
  have hlt' := arc_lt A B
  have hcr : Cross {v₁, B} {A, v₂} :=
    ⟨v₁, by simp, B, by simp, v₂, by simp, A, by simp,
      Or.inl ⟨⟨by omega, by omega⟩, by omega, by omega⟩⟩
  have hpd : ({v₁, B} : Finset (ZMod 2006)) ∈ diags D := by
    simp only [diags, Finset.mem_biUnion]
    refine ⟨T₁, hT₁, ?_⟩
    rw [Finset.mem_filter, Finset.mem_powersetCard]
    refine ⟨⟨?_, Finset.card_eq_two.mpr ⟨v₁, B, hv₁B, rfl⟩⟩, ?_⟩
    · rw [hT₁eq]; intro x hx; simp at hx ⊢; tauto
    · rw [diagPair_iff hv₁B]
      exact ⟨by omega, by omega⟩
  have hqd : ({A, v₂} : Finset (ZMod 2006)) ∈ diags D := by
    simp only [diags, Finset.mem_biUnion]
    refine ⟨T₂, hT₂, ?_⟩
    rw [Finset.mem_filter, Finset.mem_powersetCard]
    refine ⟨⟨?_, Finset.card_eq_two.mpr ⟨A, v₂, Ne.symm hv₂A, rfl⟩⟩, ?_⟩
    · rw [hT₂eq]; intro x hx; simp at hx ⊢; tauto
    · rw [diagPair_iff (Ne.symm hv₂A)]
      exact ⟨by omega, by omega⟩
  exact (noncrossPred_iff.mp hD.2.2.2.2.1) _ hpd _ hqd hcr

lemma onShortArc_contra {a b c : ZMod 2006} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (h1 : OnShortArc {a, b} c) (h2 : OnShortArc {a, c} b) : False := by
  have d1 := h1 a (by simp) b (by simp) hab
  have d2 := h2 a (by simp) c (by simp) hac
  have f1 := arc_add_arc hab
  have f2 := arc_add_arc hac
  have f3 := arc_add_arc hbc
  have g1 := arc_add_arc_eq a c b
  have g2 := arc_add_arc_eq a b c
  have g3 := arc_add_arc_eq c b a
  have g4 := arc_add_arc_eq b c a
  have g5 := arc_add_arc_eq c a b
  have g6 := arc_add_arc_eq b a c
  have p1 := arc_pos hab; have p2 := arc_pos (Ne.symm hab)
  have p3 := arc_pos hac; have p4 := arc_pos (Ne.symm hac)
  have p5 := arc_pos hbc; have p6 := arc_pos (Ne.symm hbc)
  rcases d1 with d1 | d1 <;> rcases d2 with d2 | d2 <;> omega

lemma shortTri_of_btw {D : Finset (Finset (ZMod 2006))} (_hD : IsDissection D)
    {A B v : ZMod 2006} {T : Finset (ZMod 2006)}
    (hT : T ∈ D) (hTeq : T = {v, A, B}) (hAB : A ≠ B) (hgood : arc A B % 2 = 1)
    (hbtw : Btw A v B) (hshort : arc A B ≤ 1003) : IsShortTri D {A, B} T := by
  have hvA : v ≠ A := Ne.symm hbtw.ne_left
  have hvB : v ≠ B := hbtw.ne_right
  have hsub : ({A, B} : Finset (ZMod 2006)) ⊆ T := by
    rw [hTeq]; intro x hx; simp at hx ⊢; tauto
  have e := arc_btw_sub hbtw
  have hb1 := hbtw.1
  have hb2 := hbtw.2
  have hadd := arc_add_arc hAB
  have hOSA : OnShortArc {A, B} v := by
    intro x hx y hy hxy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact absurd rfl hxy
    · left; omega
    · right; omega
    · exact absurd rfl hxy
  have hng : ng T = 2 := by
    rw [hTeq, ng_triple hvA hvB hAB]
    have hpar : min (arc A B) (arc B A) % 2 = 1 := by
      rcases min_choice (arc A B) (arc B A) with hm | hm <;> omega
    have hA := arc_add_arc hvA
    have hB := arc_add_arc hvB
    have hd := hOSA A (by simp) B (by simp) hAB
    by_cases h1 : arc v A % 2 = 1 <;> by_cases h2 : arc v B % 2 = 1 <;>
      simp [h1, h2, hgood] <;> rcases hd with hd | hd <;> omega
  refine ⟨hT, hsub, ?_, hng, ?_⟩
  · intro w hw
    rw [hTeq] at hw
    have hweq : w = v := by
      rw [Finset.mem_sdiff] at hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      tauto
    rw [hweq]; exact hOSA
  · intro hiso
    rw [hTeq, isosceles_triple hvA hvB hAB] at hiso
    have hd := hOSA A (by simp) B (by simp) hAB
    have hA := arc_add_arc hvA
    have hB := arc_add_arc hvB
    have hm : min (arc A B) (arc B A) ≤ 1003 := minArc_le A B
    have hpar : min (arc A B) (arc B A) % 2 = 1 := by
      rcases min_choice (arc A B) (arc B A) with hmc | hmc <;> omega
    have hpos1 := hbtw.1
    have hpos2 : 0 < arc v B := arc_pos hvB
    have hpos3 : 0 < arc B v := arc_pos (Ne.symm hvB)
    have hpos4 : 0 < arc v A := arc_pos hvA
    rcases hd with hd | hd
    · have m1 : minArc v A = arc A v := by unfold minArc; omega
      have m2 : minArc A B = min (arc A B) (arc B A) := rfl
      have m3 : minArc v B = arc v B := by unfold minArc; omega
      rcases hiso with h | h | h
      · rw [m1, m3] at h; omega
      · rw [m1, m2] at h; omega
      · rw [m3, m2] at h; omega
    · have m1 : minArc v A = arc v A := by unfold minArc; omega
      have m2 : minArc A B = min (arc A B) (arc B A) := rfl
      have m3 : minArc v B = arc B v := by unfold minArc; omega
      rcases hiso with h | h | h
      · rw [m1, m3] at h; omega
      · rw [m1, m2] at h; omega
      · rw [m3, m2] at h; omega

lemma exists_shortTri {D : Finset (Finset (ZMod 2006))} (hD : IsDissection D)
    {d : Finset (ZMod 2006)} (hd : d ∈ goodDiags D) : ∃ T, IsShortTri D d T := by
  obtain ⟨hdr, hgood⟩ := Finset.mem_filter.mp hd
  simp only [diags, Finset.mem_biUnion] at hdr
  obtain ⟨T₀, hT₀, hdT₀⟩ := hdr
  rw [Finset.mem_filter, Finset.mem_powersetCard] at hdT₀
  obtain ⟨⟨hdT₀sub, hd2⟩, hdiag⟩ := hdT₀
  have h2 := hD.2.2.2.1 T₀ hT₀ d (Finset.mem_powersetCard.mpr ⟨hdT₀sub, hd2⟩) hdiag
  obtain ⟨T₁, T₂, hT12, hfilt⟩ := Finset.card_eq_two.mp h2
  have hT₁ : T₁ ∈ D ∧ d ⊆ T₁ := by
    have hh : T₁ ∈ D.filter (d ⊆ ·) := by rw [hfilt]; simp
    exact Finset.mem_filter.mp hh
  have hT₂ : T₂ ∈ D ∧ d ⊆ T₂ := by
    have hh : T₂ ∈ D.filter (d ⊆ ·) := by rw [hfilt]; simp
    exact Finset.mem_filter.mp hh
  obtain ⟨A, B, hAB, rfl⟩ := Finset.card_eq_two.mp hd2
  rw [diagPair_iff hAB] at hdiag
  have hgoodAB : arc A B % 2 = 1 := (goodPair_iff hAB).mp hgood
  have hT₁3 : T₁.card = 3 := hD.1 T₁ hT₁.1
  have hT₂3 : T₂.card = 3 := hD.1 T₂ hT₂.1
  have hs1 : (T₁ \ {A, B}).card = 1 := by
    rw [Finset.card_sdiff_of_subset hT₁.2, hT₁3, hd2]
  have hs2 : (T₂ \ {A, B}).card = 1 := by
    rw [Finset.card_sdiff_of_subset hT₂.2, hT₂3, hd2]
  obtain ⟨v₁, hv₁⟩ := Finset.card_eq_one.mp hs1
  obtain ⟨v₂, hv₂⟩ := Finset.card_eq_one.mp hs2
  have hT₁eq : T₁ = {v₁, A, B} := by
    have h := Finset.union_sdiff_of_subset hT₁.2
    rw [hv₁] at h
    rw [← h]
    ext x
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    tauto
  have hT₂eq : T₂ = {v₂, A, B} := by
    have h := Finset.union_sdiff_of_subset hT₂.2
    rw [hv₂] at h
    rw [← h]
    ext x
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    tauto
  have hv₁nd : v₁ ∉ ({A, B} : Finset (ZMod 2006)) := by
    have hh : v₁ ∈ T₁ \ {A, B} := by rw [hv₁]; simp
    exact (Finset.mem_sdiff.mp hh).2
  have hv₂nd : v₂ ∉ ({A, B} : Finset (ZMod 2006)) := by
    have hh : v₂ ∈ T₂ \ {A, B} := by rw [hv₂]; simp
    exact (Finset.mem_sdiff.mp hh).2
  have hv₁A : v₁ ≠ A := by intro hh; apply hv₁nd; rw [hh]; simp
  have hv₁B : v₁ ≠ B := by intro hh; apply hv₁nd; rw [hh]; simp
  have hv₂A : v₂ ≠ A := by intro hh; apply hv₂nd; rw [hh]; simp
  have hv₂B : v₂ ≠ B := by intro hh; apply hv₂nd; rw [hh]; simp
  have hvv : v₁ ≠ v₂ := by
    intro hh; apply hT12; rw [hT₁eq, hT₂eq, hh]
  have hxor : (Btw A v₁ B ∧ ¬Btw A v₂ B) ∨ (¬Btw A v₁ B ∧ Btw A v₂ B) := by
    by_cases h1 : Btw A v₁ B
    · by_cases h2 : Btw A v₂ B
      · exfalso
        have hne : arc A v₁ ≠ arc A v₂ := by
          intro hh
          apply hvv
          have h3 : v₁ - A = v₂ - A := ZMod.val_injective 2006 hh
          exact by linear_combination h3
        rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
        · exact cross_contra hD hT₁.1 hT₂.1 hT₁eq hT₂eq h1 h2 hlt
        · exact cross_contra hD hT₂.1 hT₁.1 hT₂eq hT₁eq h2 h1 hgt
      · exact Or.inl ⟨h1, h2⟩
    · by_cases h2 : Btw A v₂ B
      · exact Or.inr ⟨h1, h2⟩
      · exfalso
        have h1' := (not_btw_iff hv₁A hv₁B hAB).mp h1
        have h2' := (not_btw_iff hv₂A hv₂B hAB).mp h2
        have hne : arc B v₁ ≠ arc B v₂ := by
          intro hh
          apply hvv
          have h3 : v₁ - B = v₂ - B := ZMod.val_injective 2006 hh
          exact by linear_combination h3
        rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
        · exact cross_contra hD hT₁.1 hT₂.1
            (by rw [hT₁eq]; congr 1; exact Finset.pair_comm _ _)
            (by rw [hT₂eq]; congr 1; exact Finset.pair_comm _ _) h1' h2' hlt
        · exact cross_contra hD hT₂.1 hT₁.1
            (by rw [hT₂eq]; congr 1; exact Finset.pair_comm _ _)
            (by rw [hT₁eq]; congr 1; exact Finset.pair_comm _ _) h2' h1' hgt
  rcases hxor with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · by_cases hs : arc A B ≤ 1003
    · exact ⟨T₁, shortTri_of_btw hD hT₁.1 hT₁eq hAB hgoodAB h1 hs⟩
    · have h2' : Btw B v₂ A := (not_btw_iff hv₂A hv₂B hAB).mp h2
      have hg : arc B A % 2 = 1 := by have hh := arc_add_arc hAB; omega
      have hs' : arc B A ≤ 1003 := by
        have hh := arc_add_arc hAB
        have hh2 := arc_lt A B
        omega
      have hcc := shortTri_of_btw hD hT₂.1
        (by rw [hT₂eq]; congr 1; exact Finset.pair_comm _ _) (Ne.symm hAB) hg h2' hs'
      rw [Finset.pair_comm B A] at hcc
      exact ⟨T₂, hcc⟩
  · by_cases hs : arc A B ≤ 1003
    · exact ⟨T₂, shortTri_of_btw hD hT₂.1 hT₂eq hAB hgoodAB h2 hs⟩
    · have h1' : Btw B v₁ A := (not_btw_iff hv₁A hv₁B hAB).mp h1
      have hg : arc B A % 2 = 1 := by have hh := arc_add_arc hAB; omega
      have hs' : arc B A ≤ 1003 := by
        have hh := arc_add_arc hAB
        have hh2 := arc_lt A B
        omega
      have hcc := shortTri_of_btw hD hT₁.1
        (by rw [hT₁eq]; congr 1; exact Finset.pair_comm _ _) (Ne.symm hAB) hg h1' hs'
      rw [Finset.pair_comm B A] at hcc
      exact ⟨T₁, hcc⟩

noncomputable def shortTri {D : Finset (Finset (ZMod 2006))} (hD : IsDissection D)
    (d : Finset (ZMod 2006)) : Finset (ZMod 2006) :=
  if h : d ∈ goodDiags D then (exists_shortTri hD h).choose else ∅

lemma shortTri_spec {D : Finset (Finset (ZMod 2006))} (hD : IsDissection D)
    {d : Finset (ZMod 2006)} (hd : d ∈ goodDiags D) :
    IsShortTri D d (shortTri hD d) := by
  show IsShortTri D d (if h : d ∈ goodDiags D then (exists_shortTri hD h).choose else ∅)
  rw [dif_pos hd]
  exact (exists_shortTri hD hd).choose_spec

lemma shortTri_injOn {D : Finset (Finset (ZMod 2006))} (hD : IsDissection D) :
    Set.InjOn (shortTri hD) (goodDiags D) := by
  intro d₁ hd₁ d₂ hd₂ heq
  by_contra hne
  have s1 := shortTri_spec hD hd₁
  have s2 := shortTri_spec hD hd₂
  rw [← heq] at s2
  have hc1 : d₁.card = 2 := by
    have h := (Finset.mem_filter.mp hd₁).1
    simp only [diags, Finset.mem_biUnion] at h
    obtain ⟨T, hT, hpT⟩ := h
    exact (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hpT).1).2
  have hc2 : d₂.card = 2 := by
    have h := (Finset.mem_filter.mp hd₂).1
    simp only [diags, Finset.mem_biUnion] at h
    obtain ⟨T, hT, hpT⟩ := h
    exact (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hpT).1).2
  have hT3 : (shortTri hD d₁).card = 3 := hD.1 _ s1.1
  obtain ⟨a, b, c, hab, hac, hbc, hTeq⟩ := Finset.card_eq_three.mp hT3
  have hp1 : d₁ ∈ ({a, b, c} : Finset (ZMod 2006)).powersetCard 2 := by
    rw [Finset.mem_powersetCard, ← hTeq]
    exact ⟨s1.2.1, hc1⟩
  have hp2 : d₂ ∈ ({a, b, c} : Finset (ZMod 2006)).powersetCard 2 := by
    rw [Finset.mem_powersetCard, ← hTeq]
    exact ⟨s2.2.1, hc2⟩
  rw [powersetCard_two_triple hab hac hbc] at hp1 hp2
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp1 hp2
  rcases hp1 with hp1 | hp1 | hp1 <;> rcases hp2 with hp2 | hp2 | hp2
  · exact absurd (hp1.trans hp2.symm) hne
  · have o1 : OnShortArc {a, b} c := by
      have hm : c ∈ (shortTri hD d₁) \ d₁ := by
        rw [hTeq, hp1, Finset.mem_sdiff]
        refine ⟨by simp, ?_⟩
        intro hh
        simp only [Finset.mem_insert, Finset.mem_singleton] at hh
        rcases hh with hh | hh
        · exact hac hh.symm
        · exact hbc hh.symm
      have hh := s1.2.2.1 c hm
      rwa [hp1] at hh
    have o2 : OnShortArc {a, c} b := by
      have hm : b ∈ (shortTri hD d₁) \ d₂ := by
        rw [hTeq, hp2, Finset.mem_sdiff]
        refine ⟨by simp, ?_⟩
        intro hh
        simp only [Finset.mem_insert, Finset.mem_singleton] at hh
        rcases hh with hh | hh
        · exact hab hh.symm
        · exact hbc hh
      have hh := s2.2.2.1 b hm
      rwa [hp2] at hh
    exact onShortArc_contra hab hac hbc o1 o2
  · have o1 : OnShortArc {a, b} c := by
      have hm : c ∈ (shortTri hD d₁) \ d₁ := by
        rw [hTeq, hp1, Finset.mem_sdiff]
        refine ⟨by simp, ?_⟩
        intro hh
        simp only [Finset.mem_insert, Finset.mem_singleton] at hh
        rcases hh with hh | hh
        · exact hac hh.symm
        · exact hbc hh.symm
      have hh := s1.2.2.1 c hm
      rwa [hp1] at hh
    have o2 : OnShortArc {b, c} a := by
      have hm : a ∈ (shortTri hD d₁) \ d₂ := by
        rw [hTeq, hp2, Finset.mem_sdiff]
        refine ⟨by simp, ?_⟩
        intro hh
        simp only [Finset.mem_insert, Finset.mem_singleton] at hh
        rcases hh with hh | hh
        · exact hab hh
        · exact hac hh
      have hh := s2.2.2.1 a hm
      rwa [hp2] at hh
    exact onShortArc_contra (Ne.symm hab) hbc hac (Finset.pair_comm a b ▸ o1) o2
  · have o1 : OnShortArc {a, c} b := by
      have hm : b ∈ (shortTri hD d₁) \ d₁ := by
        rw [hTeq, hp1, Finset.mem_sdiff]
        refine ⟨by simp, ?_⟩
        intro hh
        simp only [Finset.mem_insert, Finset.mem_singleton] at hh
        rcases hh with hh | hh
        · exact hab hh.symm
        · exact hbc hh
      have hh := s1.2.2.1 b hm
      rwa [hp1] at hh
    have o2 : OnShortArc {a, b} c := by
      have hm : c ∈ (shortTri hD d₁) \ d₂ := by
        rw [hTeq, hp2, Finset.mem_sdiff]
        refine ⟨by simp, ?_⟩
        intro hh
        simp only [Finset.mem_insert, Finset.mem_singleton] at hh
        rcases hh with hh | hh
        · exact hac hh.symm
        · exact hbc hh.symm
      have hh := s2.2.2.1 c hm
      rwa [hp2] at hh
    exact onShortArc_contra hab hac hbc o2 o1
  · exact absurd (hp1.trans hp2.symm) hne
  · have o1 : OnShortArc {a, c} b := by
      have hm : b ∈ (shortTri hD d₁) \ d₁ := by
        rw [hTeq, hp1, Finset.mem_sdiff]
        refine ⟨by simp, ?_⟩
        intro hh
        simp only [Finset.mem_insert, Finset.mem_singleton] at hh
        rcases hh with hh | hh
        · exact hab hh.symm
        · exact hbc hh
      have hh := s1.2.2.1 b hm
      rwa [hp1] at hh
    have o2 : OnShortArc {b, c} a := by
      have hm : a ∈ (shortTri hD d₁) \ d₂ := by
        rw [hTeq, hp2, Finset.mem_sdiff]
        refine ⟨by simp, ?_⟩
        intro hh
        simp only [Finset.mem_insert, Finset.mem_singleton] at hh
        rcases hh with hh | hh
        · exact hab hh
        · exact hac hh
      have hh := s2.2.2.1 a hm
      rwa [hp2] at hh
    have o1' : OnShortArc {c, a} b := Finset.pair_comm a c ▸ o1
    have o2' : OnShortArc {c, b} a := Finset.pair_comm b c ▸ o2
    exact onShortArc_contra (Ne.symm hac) (Ne.symm hbc) hab o1' o2'
  · have o1 : OnShortArc {b, c} a := by
      have hm : a ∈ (shortTri hD d₁) \ d₁ := by
        rw [hTeq, hp1, Finset.mem_sdiff]
        refine ⟨by simp, ?_⟩
        intro hh
        simp only [Finset.mem_insert, Finset.mem_singleton] at hh
        rcases hh with hh | hh
        · exact hab hh
        · exact hac hh
      have hh := s1.2.2.1 a hm
      rwa [hp1] at hh
    have o2 : OnShortArc {a, b} c := by
      have hm : c ∈ (shortTri hD d₁) \ d₂ := by
        rw [hTeq, hp2, Finset.mem_sdiff]
        refine ⟨by simp, ?_⟩
        intro hh
        simp only [Finset.mem_insert, Finset.mem_singleton] at hh
        rcases hh with hh | hh
        · exact hac hh.symm
        · exact hbc hh.symm
      have hh := s2.2.2.1 c hm
      rwa [hp2] at hh
    have o2' : OnShortArc {b, a} c := Finset.pair_comm a b ▸ o2
    exact onShortArc_contra hbc (Ne.symm hab) (Ne.symm hac) o1 o2'
  · have o1 : OnShortArc {b, c} a := by
      have hm : a ∈ (shortTri hD d₁) \ d₁ := by
        rw [hTeq, hp1, Finset.mem_sdiff]
        refine ⟨by simp, ?_⟩
        intro hh
        simp only [Finset.mem_insert, Finset.mem_singleton] at hh
        rcases hh with hh | hh
        · exact hab hh
        · exact hac hh
      have hh := s1.2.2.1 a hm
      rwa [hp1] at hh
    have o2 : OnShortArc {a, c} b := by
      have hm : b ∈ (shortTri hD d₁) \ d₂ := by
        rw [hTeq, hp2, Finset.mem_sdiff]
        refine ⟨by simp, ?_⟩
        intro hh
        simp only [Finset.mem_insert, Finset.mem_singleton] at hh
        rcases hh with hh | hh
        · exact hab hh.symm
        · exact hbc hh
      have hh := s2.2.2.1 b hm
      rwa [hp2] at hh
    have o1' : OnShortArc {c, b} a := Finset.pair_comm b c ▸ o1
    have o2' : OnShortArc {c, a} b := Finset.pair_comm a c ▸ o2
    exact onShortArc_contra (Ne.symm hbc) (Ne.symm hac) (Ne.symm hab) o1' o2'
  · exact absurd (hp1.trans hp2.symm) hne

lemma card_bad_ge {D : Finset (Finset (ZMod 2006))} (hD : IsDissection D) :
    (goodDiags D).card ≤ (D.filter fun T => ng T = 2 ∧ ¬Isosceles T).card := by
  have hinj := shortTri_injOn hD
  have him : (goodDiags D).image (shortTri hD) ⊆
      D.filter (fun T => ng T = 2 ∧ ¬Isosceles T) := by
    intro T hT
    rw [Finset.mem_image] at hT
    obtain ⟨d, hd, rfl⟩ := hT
    have h := shortTri_spec hD hd
    exact Finset.mem_filter.mpr ⟨h.1, h.2.2.2.1, h.2.2.2.2⟩
  have h1 := Finset.card_image_of_injOn hinj
  have h2 := Finset.card_le_card him
  omega

theorem upper_bound {D : Finset (Finset (ZMod 2006))} (hD : IsDissection D) :
    (D.filter IsSpecial).card ≤ 1003 := by
  have hg := card_goodish hD
  have hb := card_bad_ge hD
  have hsub : D.filter IsSpecial ⊆
      (D.filter fun T => ng T = 2) \ (D.filter fun T => ng T = 2 ∧ ¬Isosceles T) := by
    intro T hT
    rw [Finset.mem_filter] at hT
    have hng2 : ng T = 2 := by
      have hT3 := hD.1 T hT.1
      obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hT3
      have hev := ng_even hab hac hbc
      have hle := ng_le_three hab hac hbc
      have h2 := hT.2.2
      rcases hev with ⟨k, hk⟩
      omega
    rw [Finset.mem_sdiff, Finset.mem_filter]
    refine ⟨⟨hT.1, hng2⟩, ?_⟩
    rw [Finset.mem_filter]
    rintro ⟨-, -, hni⟩
    exact hni hT.2.1
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_sdiff_of_subset (by intro T hT; rw [Finset.mem_filter] at hT ⊢; exact ⟨hT.1, hT.2.1⟩),
    hg] at hcard
  omega

end charging

snip end

section construction

/-- The ear triangles `{2i, 2i+1, 2i+2}` of the extremal dissection. -/
def earTri (i : Fin 1003) : Finset (ZMod 2006) :=
  {((2 * i.val : ℕ) : ZMod 2006), ((2 * i.val + 1 : ℕ) : ZMod 2006),
   ((2 * i.val + 2 : ℕ) : ZMod 2006)}

/-- The central fan triangles `{0, 2j+2, 2j+4}` of the extremal dissection. -/
def cenTri (j : Fin 1001) : Finset (ZMod 2006) :=
  {(0 : ZMod 2006), ((2 * j.val + 2 : ℕ) : ZMod 2006), ((2 * j.val + 4 : ℕ) : ZMod 2006)}

/-- The extremal dissection: the 1003 ears together with a fan triangulation of the
central 1003-gon. -/
def D₀ : Finset (Finset (ZMod 2006)) := Finset.univ.image earTri ∪ Finset.univ.image cenTri

section noncross_manual

/-- The ear chords `{2i, 2i+2}`. -/
def earChord (i : Fin 1003) : Finset (ZMod 2006) :=
  {((2 * i.val : ℕ) : ZMod 2006), ((2 * i.val + 2 : ℕ) : ZMod 2006)}

/-- The fan chords `{0, 2k+4}`. -/
def fanChord (k : Fin 1000) : Finset (ZMod 2006) :=
  {(0 : ZMod 2006), ((2 * k.val + 4 : ℕ) : ZMod 2006)}

lemma val_parity_natCast (n : ℕ) : ((n : ZMod 2006).val) % 2 = n % 2 := by
  rw [ZMod.val_natCast]
  omega

lemma earChord_even (i : Fin 1003) : ∀ x ∈ earChord i, x.val % 2 = 0 := by
  intro x hx
  rw [earChord, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl <;> rw [val_parity_natCast] <;> omega

lemma fanChord_even (k : Fin 1000) : ∀ x ∈ fanChord k, x.val % 2 = 0 := by
  intro x hx
  rw [fanChord, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · rw [ZMod.val_zero]
  · rw [val_parity_natCast]; omega

lemma arc_ofNat_le {m n : ℕ} (hmn : m ≤ n) (_hn : n ≤ 2006) :
    arc (m : ZMod 2006) (n : ZMod 2006) = (n - m) % 2006 := by
  show ((n : ZMod 2006) - (m : ZMod 2006)).val = (n - m) % 2006
  have e : (n : ZMod 2006) - (m : ZMod 2006) = ((n - m : ℕ) : ZMod 2006) := by
    rw [← Nat.cast_sub hmn]
  rw [e, ZMod.val_natCast]

lemma pair_eq_pair {a b c d : ZMod 2006} (h : ({a, b} : Finset (ZMod 2006)) = {c, d}) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  have h2 := Finset.coe_inj.mpr h
  simp only [Finset.coe_insert, Finset.coe_singleton] at h2
  exact Set.pair_eq_pair_iff.mp h2

lemma arc_earChord (i : Fin 1003) :
    arc ((2 * i.val : ℕ) : ZMod 2006) ((2 * i.val + 2 : ℕ) : ZMod 2006) = 2 := by
  rw [arc_ofNat_le (by omega) (by have := i.2; omega)]
  omega

lemma earTri_ne (i : Fin 1003) :
    ((2 * i.val : ℕ) : ZMod 2006) ≠ ((2 * i.val + 1 : ℕ) : ZMod 2006) ∧
    ((2 * i.val : ℕ) : ZMod 2006) ≠ ((2 * i.val + 2 : ℕ) : ZMod 2006) ∧
    ((2 * i.val + 1 : ℕ) : ZMod 2006) ≠ ((2 * i.val + 2 : ℕ) : ZMod 2006) := by
  have hb := i.2
  refine ⟨?_, ?_, ?_⟩ <;>
  · intro hh
    have g := congrArg ZMod.val hh
    rw [ZMod.val_natCast, ZMod.val_natCast] at g
    omega

lemma cenTri_ne (j : Fin 1001) :
    (0 : ZMod 2006) ≠ ((2 * j.val + 2 : ℕ) : ZMod 2006) ∧
    (0 : ZMod 2006) ≠ ((2 * j.val + 4 : ℕ) : ZMod 2006) ∧
    ((2 * j.val + 2 : ℕ) : ZMod 2006) ≠ ((2 * j.val + 4 : ℕ) : ZMod 2006) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hh
    have g := congrArg ZMod.val hh
    rw [ZMod.val_zero, ZMod.val_natCast] at g
    have := j.2; omega
  · intro hh
    have g := congrArg ZMod.val hh
    rw [ZMod.val_zero, ZMod.val_natCast] at g
    have := j.2; omega
  · intro hh
    have g := congrArg ZMod.val hh
    rw [ZMod.val_natCast, ZMod.val_natCast] at g
    have := j.2; omega

lemma not_btw_of_even {x y z : ZMod 2006} (hx : x.val % 2 = 0) (hy : y.val % 2 = 0)
    (hz : arc x z = 2) : ¬Btw x y z := by
  intro h
  have h1 : arc x y = 1 := by
    have g1 := h.1; have g2 := h.2
    omega
  have h2 : (y - x).val = 1 := h1
  rcases le_total x.val y.val with hle | hle
  · have h3 := ZMod.val_sub (n := 2006) (a := y) (b := x) hle
    omega
  · have h4 : (x - y).val = x.val - y.val := ZMod.val_sub (n := 2006) (a := x) (b := y) hle
    have hne : x - y ≠ 0 := by
      intro hh
      have hh2 : x = y := sub_eq_zero.mp hh
      rw [hh2, sub_self] at h2
      simp at h2
    haveI : NeZero (x - y) := ⟨hne⟩
    have h6 : (y - x) = -(x - y) := by abel
    have h5 : (y - x).val = 2006 - (x - y).val := by rw [h6, ZMod.val_neg_of_ne_zero]
    omega

lemma Btw.not_self_left {a b : ZMod 2006} : ¬ Btw a a b := by
  intro h
  have h1 := h.1
  rw [arc_self] at h1
  exact absurd h1 (lt_irrefl 0)

lemma Btw.not_self_right {a b : ZMod 2006} : ¬ Btw a b a := by
  intro h
  have h2 := h.2
  rw [arc_self] at h2
  exact absurd h2 (Nat.not_lt_zero _)

lemma Btw.not_self_mid {a b : ZMod 2006} : ¬ Btw a b b := by
  intro h
  exact absurd h.2 (lt_irrefl _)

/-- An ear chord crosses no chord with even-valued endpoints. -/
lemma not_cross_earChord_left {i : Fin 1003} {q : Finset (ZMod 2006)}
    (hq : ∀ x ∈ q, x.val % 2 = 0) : ¬ Cross (earChord i) q := by
  rintro ⟨a, ha, b, hb, c, hc, d, hd, h⟩
  rw [earChord, Finset.mem_insert, Finset.mem_singleton] at ha hb
  have hA : (((2 * i.val : ℕ) : ZMod 2006).val) % 2 = 0 := by rw [val_parity_natCast]; omega
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · rcases h with h | h
    · exact absurd h.1 Btw.not_self_right
    · exact absurd h.1 Btw.not_self_right
  · rcases h with h | h
    · exact not_btw_of_even hA (hq _ hc) (arc_earChord i) h.1
    · exact not_btw_of_even hA (hq _ hd) (arc_earChord i) h.1
  · rcases h with h | h
    · exact not_btw_of_even hA (hq _ hd) (arc_earChord i) h.2
    · exact not_btw_of_even hA (hq _ hc) (arc_earChord i) h.2
  · rcases h with h | h
    · exact absurd h.1 Btw.not_self_right
    · exact absurd h.1 Btw.not_self_right

/-- Crossing of chords is symmetric. -/
lemma cross_comm {p q : Finset (ZMod 2006)} (h : Cross p q) : Cross q p := by
  obtain ⟨a, ha, b, hb, c, hc, d, hd, h⟩ := h
  have hab : a ≠ b := by
    intro hh; subst hh
    rcases h with h | h
    · exact absurd h.1 Btw.not_self_right
    · exact absurd h.1 Btw.not_self_right
  have hcd : c ≠ d := by
    intro hh; subst hh
    rcases h with h | h <;>
      exact absurd h.1 ((not_btw_iff (Ne.symm h.1.ne_left) h.1.ne_right hab).mpr h.2)
  rcases h with h | h
  · -- cyclic order a, c, b, d
    refine ⟨c, hc, d, hd, b, hb, a, ha, Or.inl ⟨?_, ?_⟩⟩
    · -- Btw c b d
      have e1 := arc_btw_sub h.1
      have hac : a ≠ c := h.1.ne_left
      have hcb : c ≠ b := h.1.ne_right
      have hbd : b ≠ d := h.2.ne_left
      have hda : d ≠ a := h.2.ne_right
      have hadd := arc_add_arc hab
      have g1 := arc_add_arc_eq c b d
      have p1 := h.1.1; have p2 := h.1.2; have p3 := h.2.1; have p4 := h.2.2
      have q1 := arc_pos hac; have q2 := arc_pos hbd
      have q3 := arc_pos (Ne.symm hac); have q4 := arc_pos (Ne.symm hcb)
      have q5 := arc_pos (Ne.symm hbd); have q6 := arc_pos (Ne.symm hda)
      have l1 := arc_lt c b; have l2 := arc_lt b d
      constructor <;> omega
    · -- Btw d a c
      have e1 := arc_btw_sub h.1
      have e2 := arc_btw_sub h.2
      have hac : a ≠ c := h.1.ne_left
      have hcb : c ≠ b := h.1.ne_right
      have hbd : b ≠ d := h.2.ne_left
      have hda : d ≠ a := h.2.ne_right
      have hadd := arc_add_arc hab
      have hadd2 := arc_add_arc hcd
      have g1 := arc_add_arc_eq c b d
      have p1 := h.1.1; have p2 := h.1.2; have p3 := h.2.1; have p4 := h.2.2
      have q1 := arc_pos hac; have q2 := arc_pos hbd
      have q3 := arc_pos (Ne.symm hac); have q4 := arc_pos (Ne.symm hcb)
      have q5 := arc_pos (Ne.symm hbd); have q6 := arc_pos (Ne.symm hda)
      have q7 := arc_pos hda; have q8 := arc_pos hcb
      have l1 := arc_lt c b; have l2 := arc_lt b d
      constructor <;> omega
  · -- cyclic order a, d, b, c
    refine ⟨c, hc, d, hd, a, ha, b, hb, Or.inl ⟨?_, ?_⟩⟩
    · -- Btw c a d
      have e1 := arc_btw_sub h.2
      have had : a ≠ d := h.1.ne_left
      have hdb : d ≠ b := h.1.ne_right
      have hbc : b ≠ c := h.2.ne_left
      have hca : c ≠ a := h.2.ne_right
      have hadd := arc_add_arc hab
      have hadd2 := arc_add_arc hca
      have g1 := arc_add_arc_eq c a d
      have p1 := h.1.1; have p2 := h.1.2; have p3 := h.2.1; have p4 := h.2.2
      have q1 := arc_pos had; have q2 := arc_pos hbc
      have q3 := arc_pos (Ne.symm had); have q4 := arc_pos (Ne.symm hdb)
      have q5 := arc_pos (Ne.symm hbc); have q6 := arc_pos (Ne.symm hca)
      have q7 := arc_pos hca; have q8 := arc_pos hdb
      have l1 := arc_lt a d; have l2 := arc_lt b c
      constructor <;> omega
    · -- Btw d b c
      have e1 := arc_btw_sub h.1
      have e2 := arc_btw_sub h.2
      have had : a ≠ d := h.1.ne_left
      have hdb : d ≠ b := h.1.ne_right
      have hbc : b ≠ c := h.2.ne_left
      have hca : c ≠ a := h.2.ne_right
      have hadd := arc_add_arc hab
      have hadd2 := arc_add_arc hcd
      have g1 := arc_add_arc_eq c a d
      have g2 := arc_add_arc_eq a d b
      have p1 := h.1.1; have p2 := h.1.2; have p3 := h.2.1; have p4 := h.2.2
      have q1 := arc_pos had; have q2 := arc_pos hbc
      have q3 := arc_pos (Ne.symm had); have q4 := arc_pos (Ne.symm hdb)
      have q5 := arc_pos (Ne.symm hbc); have q6 := arc_pos (Ne.symm hca)
      have q7 := arc_pos hca; have q8 := arc_pos hdb
      have q9 := arc_pos had
      have l1 := arc_lt a d; have l2 := arc_lt b c
      constructor <;> omega

/-- Two fan chords share the endpoint `0`, hence do not cross; the only nontrivial
case is settled by value arithmetic. -/
lemma fan_fan_aux {k k' : Fin 1000}
    (h1 : Btw 0 ((2 * k'.val + 4 : ℕ) : ZMod 2006) ((2 * k.val + 4 : ℕ) : ZMod 2006))
    (h2 : Btw ((2 * k.val + 4 : ℕ) : ZMod 2006) ((2 * k'.val + 4 : ℕ) : ZMod 2006) 0) :
    False := by
  have hF : arc 0 ((2 * k.val + 4 : ℕ) : ZMod 2006) = 2 * k.val + 4 := by
    show (((2 * k.val + 4 : ℕ) : ZMod 2006) - 0).val = _
    rw [sub_zero, ZMod.val_natCast, Nat.mod_eq_of_lt (by have := k.2; omega)]
  have hF' : arc 0 ((2 * k'.val + 4 : ℕ) : ZMod 2006) = 2 * k'.val + 4 := by
    show (((2 * k'.val + 4 : ℕ) : ZMod 2006) - 0).val = _
    rw [sub_zero, ZMod.val_natCast, Nat.mod_eq_of_lt (by have := k'.2; omega)]
  have hlt : k'.val < k.val := by
    have g := h1.2
    omega
  have hFF' : arc ((2 * k.val + 4 : ℕ) : ZMod 2006) ((2 * k'.val + 4 : ℕ) : ZMod 2006) =
      2006 - 2 * (k.val - k'.val) := by
    show (((2 * k'.val + 4 : ℕ) : ZMod 2006) - ((2 * k.val + 4 : ℕ) : ZMod 2006)).val = _
    have e : ((2 * k'.val + 4 : ℕ) : ZMod 2006) - ((2 * k.val + 4 : ℕ) : ZMod 2006) =
        ((2006 - 2 * (k.val - k'.val) : ℕ) : ZMod 2006) := by
      have hk1 : ((2006 - 2 * (k.val - k'.val) : ℕ) : ZMod 2006) =
          (2006 : ZMod 2006) - 2 * ((k.val : ZMod 2006) - (k'.val : ZMod 2006)) := by
        rw [Nat.cast_sub (by omega : 2 * (k.val - k'.val) ≤ 2006), Nat.cast_mul,
          Nat.cast_sub (by omega : k'.val ≤ k.val)]
        norm_num
      rw [hk1, show (2006 : ZMod 2006) = 0 from ZMod.natCast_self 2006]
      push_cast
      ring
    rw [e, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  have hF0 : arc ((2 * k.val + 4 : ℕ) : ZMod 2006) 0 = 2002 - 2 * k.val := by
    show (0 - ((2 * k.val + 4 : ℕ) : ZMod 2006)).val = _
    have hne : ((2 * k.val + 4 : ℕ) : ZMod 2006) ≠ 0 := by
      intro hh
      have hv : (((2 * k.val + 4 : ℕ) : ZMod 2006).val) = 0 := by rw [hh, ZMod.val_zero]
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by have := k.2; omega)] at hv
      have := k.2
      omega
    haveI : NeZero ((2 * k.val + 4 : ℕ) : ZMod 2006) := ⟨hne⟩
    rw [zero_sub, ZMod.val_neg_of_ne_zero, ZMod.val_natCast,
      Nat.mod_eq_of_lt (by have := k.2; omega)]
    have := k.2
    omega
  have g1 := h2.1; have g2 := h2.2
  have g3 := h1.1
  omega

lemma not_cross_fan_self {k k' : Fin 1000} : ¬ Cross (fanChord k) (fanChord k') := by
  rintro ⟨a, ha, b, hb, c, hc, d, hd, h⟩
  rw [fanChord, Finset.mem_insert, Finset.mem_singleton] at ha hb hc hd
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    rcases hc with rfl | rfl <;> rcases hd with rfl | rfl
  · rcases h with h | h
    · exact absurd h.1 Btw.not_self_left
    · exact absurd h.1 Btw.not_self_left
  · rcases h with h | h
    · exact absurd h.1 Btw.not_self_left
    · exact absurd h.1 Btw.not_self_right
  · rcases h with h | h
    · exact absurd h.1 Btw.not_self_right
    · exact absurd h.1 Btw.not_self_left
  · rcases h with h | h
    · exact absurd h.1 Btw.not_self_right
    · exact absurd h.1 Btw.not_self_right
  · rcases h with h | h
    · exact absurd h.1 Btw.not_self_left
    · exact absurd h.1 Btw.not_self_left
  · rcases h with h | h
    · exact absurd h.1 Btw.not_self_left
    · exact absurd h.2 Btw.not_self_mid
  · rcases h with h | h
    · exact absurd h.2 Btw.not_self_mid
    · exact absurd h.1 Btw.not_self_left
  · rcases h with h | h <;> exact fan_fan_aux h.1 h.2
  · rcases h with h | h
    · exact absurd h.1 Btw.not_self_mid
    · exact absurd h.1 Btw.not_self_mid
  · rcases h with h | h
    · exact absurd h.1 Btw.not_self_mid
    · exact absurd h.2 Btw.not_self_left
  · rcases h with h | h
    · exact absurd h.2 Btw.not_self_left
    · exact absurd h.1 Btw.not_self_mid
  · rcases h with h | h <;> exact fan_fan_aux h.2 h.1
  · rcases h with h | h
    · exact absurd h.1 Btw.not_self_right
    · exact absurd h.1 Btw.not_self_right
  · rcases h with h | h
    · exact absurd h.1 Btw.not_self_right
    · exact absurd h.1 Btw.not_self_right
  · rcases h with h | h
    · exact absurd h.1 Btw.not_self_right
    · exact absurd h.1 Btw.not_self_right
  · rcases h with h | h
    · exact absurd h.1 Btw.not_self_right
    · exact absurd h.1 Btw.not_self_right

/-- The diagonals of the extremal dissection, in closed form. -/
lemma diags_D₀ : diags D₀ = Finset.univ.image earChord ∪ Finset.univ.image fanChord := by
  ext p
  simp only [diags, Finset.mem_biUnion, Finset.mem_filter,
    Finset.mem_union, Finset.mem_image, D₀]
  constructor
  · rintro ⟨T, hT, hp2, hdiag⟩
    rcases hT with ⟨i, -, rfl⟩ | ⟨j, -, rfl⟩
    · rw [show earTri i = {((2 * i.val : ℕ) : ZMod 2006), ((2 * i.val + 1 : ℕ) : ZMod 2006),
        ((2 * i.val + 2 : ℕ) : ZMod 2006)} from rfl,
        powersetCard_two_triple (earTri_ne i).1 (earTri_ne i).2.1 (earTri_ne i).2.2,
        Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hp2
      rcases hp2 with rfl | rfl | rfl
      · exfalso
        rw [diagPair_iff (earTri_ne i).1] at hdiag
        have h1 : arc ((2 * i.val : ℕ) : ZMod 2006) ((2 * i.val + 1 : ℕ) : ZMod 2006) = 1 := by
          rw [arc_ofNat_le (by omega) (by have := i.2; omega)]; omega
        exact hdiag.1 h1
      · left
        exact ⟨i, Finset.mem_univ _, rfl⟩
      · exfalso
        rw [diagPair_iff (earTri_ne i).2.2] at hdiag
        have h1 : arc ((2 * i.val + 1 : ℕ) : ZMod 2006) ((2 * i.val + 2 : ℕ) : ZMod 2006) = 1 := by
          rw [arc_ofNat_le (by omega) (by have := i.2; omega)]; omega
        exact hdiag.1 h1
    · rw [show cenTri j = {(0 : ZMod 2006), ((2 * j.val + 2 : ℕ) : ZMod 2006),
        ((2 * j.val + 4 : ℕ) : ZMod 2006)} from rfl,
        powersetCard_two_triple (cenTri_ne j).1 (cenTri_ne j).2.1 (cenTri_ne j).2.2,
        Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hp2
      rcases hp2 with rfl | rfl | rfl
      · -- p = {0, ↑(2j+2)}
        by_cases hj0 : j.val = 0
        · left
          refine ⟨⟨0, by omega⟩, Finset.mem_univ _, ?_⟩
          rw [hj0]
          rfl
        · right
          refine ⟨⟨j.val - 1, by have := j.2; omega⟩, Finset.mem_univ _, ?_⟩
          ext x
          simp only [fanChord, Finset.mem_insert, Finset.mem_singleton]
          have e : ((2 * (j.val - 1) + 4 : ℕ) : ZMod 2006) = ((2 * j.val + 2 : ℕ) : ZMod 2006) := by
            have e2 : (2 * (j.val - 1) + 4 : ℕ) = 2 * j.val + 2 := by omega
            rw [e2]
          rw [e]
      · -- p = {0, ↑(2j+4)}
        by_cases hj : j.val ≤ 999
        · right
          refine ⟨⟨j.val, by omega⟩, Finset.mem_univ _, rfl⟩
        · left
          have hj2 : j.val = 1000 := by have := j.2; omega
          refine ⟨⟨1002, by norm_num⟩, Finset.mem_univ _, ?_⟩
          ext x
          simp only [earChord, Finset.mem_insert, Finset.mem_singleton]
          have e : ((2 * (1002 : ℕ) + 2 : ℕ) : ZMod 2006) = (0 : ZMod 2006) := by
            decide
          have e2 : ((2 * (1002 : ℕ) : ℕ) : ZMod 2006) = ((2 * 1000 + 4 : ℕ) : ZMod 2006) := by
            norm_num
          rw [hj2, e, e2]
          exact Or.comm
      · -- p = {↑(2j+2), ↑(2j+4)} = earChord (j+1)
        left
        refine ⟨⟨j.val + 1, by have := j.2; omega⟩, Finset.mem_univ _, ?_⟩
        ext x
        simp only [earChord, Finset.mem_insert, Finset.mem_singleton]
        have e1 : ((2 * (j.val + 1) : ℕ) : ZMod 2006) = ((2 * j.val + 2 : ℕ) : ZMod 2006) := by
          have e2 : (2 * (j.val + 1) : ℕ) = 2 * j.val + 2 := by omega
          rw [e2]
        have e2 : ((2 * (j.val + 1) + 2 : ℕ) : ZMod 2006) = ((2 * j.val + 4 : ℕ) : ZMod 2006) := by
          have e3 : (2 * (j.val + 1) + 2 : ℕ) = 2 * j.val + 4 := by omega
          rw [e3]
        rw [e1, e2]
  · rintro (⟨i, -, rfl⟩ | ⟨k, -, rfl⟩)
    · -- p = earChord i: contained in earTri i
      refine ⟨earTri i, Or.inl ⟨i, Finset.mem_univ _, rfl⟩, ?_, ?_⟩
      · rw [show earTri i = {((2 * i.val : ℕ) : ZMod 2006), ((2 * i.val + 1 : ℕ) : ZMod 2006),
          ((2 * i.val + 2 : ℕ) : ZMod 2006)} from rfl,
          powersetCard_two_triple (earTri_ne i).1 (earTri_ne i).2.1 (earTri_ne i).2.2,
          Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]
        exact Or.inr (Or.inl rfl)
      · show IsDiag {((2 * i.val : ℕ) : ZMod 2006), ((2 * i.val + 2 : ℕ) : ZMod 2006)}
        rw [diagPair_iff (earTri_ne i).2.1]
        constructor
        · rw [arc_earChord i]; norm_num
        · rw [arc_earChord i]; norm_num
    · -- p = fanChord k: contained in cenTri (k+1)
      have hk : k.val + 1 < 1001 := by have := k.2; omega
      refine ⟨cenTri ⟨k.val + 1, hk⟩, Or.inr ⟨⟨k.val + 1, hk⟩, Finset.mem_univ _, rfl⟩, ?_, ?_⟩
      · have hk2 : cenTri ⟨k.val + 1, hk⟩ = {(0 : ZMod 2006), ((2 * (k.val + 1) + 2 : ℕ) : ZMod 2006),
          ((2 * (k.val + 1) + 4 : ℕ) : ZMod 2006)} := rfl
        have hne := cenTri_ne ⟨k.val + 1, hk⟩
        have hval : (⟨k.val + 1, hk⟩ : Fin 1001).val = k.val + 1 := rfl
        rw [hval] at hne
        rw [hk2,
          powersetCard_two_triple hne.1 hne.2.1 hne.2.2, Finset.mem_insert, Finset.mem_insert,
          Finset.mem_singleton]
        have e : ((2 * (k.val + 1) + 2 : ℕ) : ZMod 2006) = ((2 * k.val + 4 : ℕ) : ZMod 2006) := by
          have e2 : (2 * (k.val + 1) + 2 : ℕ) = 2 * k.val + 4 := by ring
          rw [e2]
        rw [e]
        exact Or.inl rfl
      · show IsDiag {(0 : ZMod 2006), ((2 * k.val + 4 : ℕ) : ZMod 2006)}
        have h0ne : (0 : ZMod 2006) ≠ ((2 * k.val + 4 : ℕ) : ZMod 2006) := by
          intro hh
          have g := congrArg ZMod.val hh
          rw [ZMod.val_zero, ZMod.val_natCast] at g
          have := k.2
          omega
        rw [diagPair_iff h0ne]
        constructor <;> intro hh
        · have h1 : arc (0 : ZMod 2006) ((2 * k.val + 4 : ℕ) : ZMod 2006) = 2 * k.val + 4 := by
            show (((2 * k.val + 4 : ℕ) : ZMod 2006) - 0).val = 2 * k.val + 4
            rw [sub_zero, ZMod.val_natCast, Nat.mod_eq_of_lt (by have := k.2; omega)]
          omega
        · have h1 : arc (0 : ZMod 2006) ((2 * k.val + 4 : ℕ) : ZMod 2006) = 2 * k.val + 4 := by
            show (((2 * k.val + 4 : ℕ) : ZMod 2006) - 0).val = 2 * k.val + 4
            rw [sub_zero, ZMod.val_natCast, Nat.mod_eq_of_lt (by have := k.2; omega)]
          omega

lemma construction_noncross : noncrossPred (diags D₀) := by
  rw [diags_D₀, noncrossPred_iff]
  intro p hp q hq hcr
  rw [Finset.mem_union] at hp hq
  rcases hp with hp | hp
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hp
    rcases hq with hq | hq
    · obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hq
      exact not_cross_earChord_left (earChord_even j) hcr
    · obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hq
      exact not_cross_earChord_left (fanChord_even k) hcr
  · obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hp
    rcases hq with hq | hq
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hq
      exact not_cross_earChord_left (fanChord_even k) (cross_comm hcr)
    · obtain ⟨k', -, rfl⟩ := Finset.mem_image.mp hq
      exact not_cross_fan_self hcr

lemma ng_earTri (i : Fin 1003) : ng (earTri i) = 2 := by
  have hne := earTri_ne i
  show ng {((2 * i.val : ℕ) : ZMod 2006), ((2 * i.val + 1 : ℕ) : ZMod 2006),
    ((2 * i.val + 2 : ℕ) : ZMod 2006)} = 2
  rw [ng_triple hne.1 hne.2.1 hne.2.2]
  have h01 : arc ((2 * i.val : ℕ) : ZMod 2006) ((2 * i.val + 1 : ℕ) : ZMod 2006) = 1 := by
    rw [arc_ofNat_le (by omega) (by have := i.2; omega)]; omega
  have h02 : arc ((2 * i.val : ℕ) : ZMod 2006) ((2 * i.val + 2 : ℕ) : ZMod 2006) = 2 :=
    arc_earChord i
  have h12 : arc ((2 * i.val + 1 : ℕ) : ZMod 2006) ((2 * i.val + 2 : ℕ) : ZMod 2006) = 1 := by
    rw [arc_ofNat_le (by omega) (by have := i.2; omega)]; omega
  rw [h01, h02, h12]
  norm_num

lemma isosceles_earTri (i : Fin 1003) : Isosceles (earTri i) := by
  have hne := earTri_ne i
  show Isosceles {((2 * i.val : ℕ) : ZMod 2006), ((2 * i.val + 1 : ℕ) : ZMod 2006),
    ((2 * i.val + 2 : ℕ) : ZMod 2006)}
  rw [isosceles_triple hne.1 hne.2.1 hne.2.2]
  right; left
  have h01 : arc ((2 * i.val : ℕ) : ZMod 2006) ((2 * i.val + 1 : ℕ) : ZMod 2006) = 1 := by
    rw [arc_ofNat_le (by omega) (by have := i.2; omega)]; omega
  have h10 : arc ((2 * i.val + 1 : ℕ) : ZMod 2006) ((2 * i.val : ℕ) : ZMod 2006) = 2005 := by
    have h := arc_add_arc hne.1
    omega
  have h12 : arc ((2 * i.val + 1 : ℕ) : ZMod 2006) ((2 * i.val + 2 : ℕ) : ZMod 2006) = 1 := by
    rw [arc_ofNat_le (by omega) (by have := i.2; omega)]; omega
  have h21 : arc ((2 * i.val + 2 : ℕ) : ZMod 2006) ((2 * i.val + 1 : ℕ) : ZMod 2006) = 2005 := by
    have h := arc_add_arc hne.2.2
    omega
  have m1 : minArc ((2 * i.val : ℕ) : ZMod 2006) ((2 * i.val + 1 : ℕ) : ZMod 2006) = 1 := by
    unfold minArc
    rw [h01, h10]
    norm_num
  have m2 : minArc ((2 * i.val + 1 : ℕ) : ZMod 2006) ((2 * i.val + 2 : ℕ) : ZMod 2006) = 1 := by
    unfold minArc
    rw [h12, h21]
    norm_num
  rw [m1, m2]

lemma special_earTri (i : Fin 1003) : IsSpecial (earTri i) :=
  ⟨isosceles_earTri i, by rw [ng_earTri i]⟩

lemma not_special_cenTri (j : Fin 1001) : ¬ IsSpecial (cenTri j) := by
  intro hs
  have hne := cenTri_ne j
  have hng : ng (cenTri j) = 0 := by
    show ng {(0 : ZMod 2006), ((2 * j.val + 2 : ℕ) : ZMod 2006),
      ((2 * j.val + 4 : ℕ) : ZMod 2006)} = 0
    rw [ng_triple hne.1 hne.2.1 hne.2.2]
    have h02 : arc (0 : ZMod 2006) ((2 * j.val + 2 : ℕ) : ZMod 2006) = 2 * j.val + 2 := by
      show (((2 * j.val + 2 : ℕ) : ZMod 2006) - 0).val = 2 * j.val + 2
      rw [sub_zero, ZMod.val_natCast, Nat.mod_eq_of_lt (by have := j.2; omega)]
    have h04 : arc (0 : ZMod 2006) ((2 * j.val + 4 : ℕ) : ZMod 2006) = 2 * j.val + 4 := by
      show (((2 * j.val + 4 : ℕ) : ZMod 2006) - 0).val = 2 * j.val + 4
      rw [sub_zero, ZMod.val_natCast, Nat.mod_eq_of_lt (by have := j.2; omega)]
    have h24 : arc ((2 * j.val + 2 : ℕ) : ZMod 2006) ((2 * j.val + 4 : ℕ) : ZMod 2006) = 2 := by
      rw [arc_ofNat_le (by omega) (by have := j.2; omega)]; omega
    have e2 : (2 * j.val + 2) % 2 = 0 := by omega
    have e4 : (2 * j.val + 4) % 2 = 0 := by omega
    rw [h02, h04, h24, e2, e4]
    norm_num
  exact absurd hs.2 (by rw [hng]; norm_num)

lemma filter_special_D₀ : D₀.filter IsSpecial = Finset.univ.image earTri := by
  ext T
  simp only [D₀, Finset.mem_filter, Finset.mem_image, Finset.mem_union]
  constructor
  · rintro ⟨hT, hs⟩
    rcases hT with hT | hT
    · obtain ⟨i, hi, rfl⟩ := hT
      exact ⟨i, hi, rfl⟩
    · obtain ⟨j, hj, rfl⟩ := hT
      exact absurd hs (not_special_cenTri j)
  · rintro ⟨i, hi, rfl⟩
    exact ⟨Or.inl ⟨i, hi, rfl⟩, special_earTri i⟩

lemma earTri_injective : Function.Injective earTri := by
  intro i i' hh
  have h1 : ((2 * i.val + 1 : ℕ) : ZMod 2006) ∈ earTri i' := by
    rw [← hh]; simp [earTri]
  rw [earTri, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at h1
  have hb := i.2; have hb' := i'.2
  rcases h1 with h1 | h1 | h1
  · exfalso
    have g := congrArg (fun x : ZMod 2006 => x.val % 2) h1
    rw [val_parity_natCast, val_parity_natCast] at g
    omega
  · have g := congrArg ZMod.val h1
    rw [ZMod.val_natCast, ZMod.val_natCast] at g
    have hiv : i.val = i'.val := by omega
    exact Fin.ext hiv
  · exfalso
    have g := congrArg (fun x : ZMod 2006 => x.val % 2) h1
    rw [val_parity_natCast, val_parity_natCast] at g
    omega

lemma cenTri_injective : Function.Injective cenTri := by
  intro j j' hh
  have h1 : ((2 * j.val + 2 : ℕ) : ZMod 2006) ∈ cenTri j' := by
    rw [← hh, cenTri]; simp
  rw [cenTri, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at h1
  have hb := j.2; have hb' := j'.2
  rcases h1 with h1 | h1 | h1
  · exfalso
    have g := congrArg ZMod.val h1
    rw [ZMod.val_natCast, ZMod.val_zero] at g
    omega
  · have g := congrArg ZMod.val h1
    rw [ZMod.val_natCast, ZMod.val_natCast] at g
    have hjv : j.val = j'.val := by omega
    exact Fin.ext hjv
  · have h2 : ((2 * j.val + 4 : ℕ) : ZMod 2006) ∈ cenTri j' := by
      rw [← hh, cenTri]; simp
    rw [cenTri, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at h2
    rcases h2 with h2 | h2 | h2
    · exfalso
      have g2 := congrArg ZMod.val h2
      rw [ZMod.val_natCast, show (0 : ZMod 2006).val = 0 from ZMod.val_zero] at g2
      omega
    · have g := congrArg ZMod.val h1
      rw [ZMod.val_natCast, ZMod.val_natCast] at g
      have g2 := congrArg ZMod.val h2
      rw [ZMod.val_natCast, ZMod.val_natCast] at g2
      have hjv : j.val = j'.val := by omega
      exact Fin.ext hjv
    · have g2 := congrArg ZMod.val h2
      rw [ZMod.val_natCast, ZMod.val_natCast] at g2
      have hjv : j.val = j'.val := by omega
      exact Fin.ext hjv

lemma not_earTri_eq_cenTri {i : Fin 1003} {j : Fin 1001} : earTri i ≠ cenTri j := by
  intro hh
  have h1 : ((2 * i.val + 1 : ℕ) : ZMod 2006) ∈ cenTri j := by
    rw [← hh, earTri]; simp
  rw [cenTri, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at h1
  rcases h1 with h1 | h1 | h1
  · have g := congrArg (fun x : ZMod 2006 => x.val % 2) h1
    rw [val_parity_natCast, ZMod.val_zero] at g
    omega
  · have g := congrArg (fun x : ZMod 2006 => x.val % 2) h1
    rw [val_parity_natCast, val_parity_natCast] at g
    omega
  · have g := congrArg (fun x : ZMod 2006 => x.val % 2) h1
    rw [val_parity_natCast, val_parity_natCast] at g
    omega

lemma card3_mem_D₀ : ∀ T ∈ D₀, T.card = 3 := by
  intro T hT
  simp only [D₀, Finset.mem_union, Finset.mem_image] at hT
  rcases hT with ⟨i, -, rfl⟩ | ⟨j, -, rfl⟩
  · exact Finset.card_eq_three.mpr ⟨_, _, _, (earTri_ne i).1, (earTri_ne i).2.1,
      (earTri_ne i).2.2, rfl⟩
  · exact Finset.card_eq_three.mpr ⟨_, _, _, (cenTri_ne j).1, (cenTri_ne j).2.1,
      (cenTri_ne j).2.2, rfl⟩

lemma card_D₀ : D₀.card = 2004 := by
  have hdisj : Disjoint (Finset.univ.image earTri) (Finset.univ.image cenTri) := by
    rw [Finset.disjoint_left]
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨i, -, rfl⟩ := hx
    rw [Finset.mem_image]
    intro hxc
    obtain ⟨j, -, hjj⟩ := hxc
    exact not_earTri_eq_cenTri hjj.symm
  show (Finset.univ.image earTri ∪ Finset.univ.image cenTri).card = 2004
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ earTri_injective,
    Finset.card_image_of_injective _ cenTri_injective, Finset.card_univ, Finset.card_univ,
    Fintype.card_fin, Fintype.card_fin]

lemma earChord_injective : Function.Injective earChord := by
  intro i i' hh
  have h1 : ((2 * i.val : ℕ) : ZMod 2006) ∈ earChord i' := by
    rw [← hh, earChord]; simp
  rw [earChord, Finset.mem_insert, Finset.mem_singleton] at h1
  have hb := i.2; have hb' := i'.2
  rcases h1 with h1 | h1
  · have g := congrArg ZMod.val h1
    rw [ZMod.val_natCast, ZMod.val_natCast] at g
    have hiv : i.val = i'.val := by omega
    exact Fin.ext hiv
  · -- ↑(2i) = ↑(2i'+2): then use the other element
    have h2 : ((2 * i.val + 2 : ℕ) : ZMod 2006) ∈ earChord i' := by
      rw [← hh, earChord]; simp
    rw [earChord, Finset.mem_insert, Finset.mem_singleton] at h2
    rcases h2 with h2 | h2
    · -- ↑(2i+2) = ↑(2i'): 2i+2 ≡ 2i' ∧ 2i ≡ 2i'+2 (mod 2006) → contradiction
      exfalso
      have g := congrArg ZMod.val h1
      rw [ZMod.val_natCast, ZMod.val_natCast] at g
      have g2 := congrArg ZMod.val h2
      rw [ZMod.val_natCast, ZMod.val_natCast] at g2
      omega
    · -- ↑(2i+2) = ↑(2i'+2): 2i+2 ≡ 2i'+2 ∧ 2i ≡ 2i'+2 → contradiction
      exfalso
      have g := congrArg ZMod.val h1
      rw [ZMod.val_natCast, ZMod.val_natCast] at g
      have g2 := congrArg ZMod.val h2
      rw [ZMod.val_natCast, ZMod.val_natCast] at g2
      omega

lemma fanChord_injective : Function.Injective fanChord := by
  intro k k' hh
  have h1 : ((2 * k.val + 4 : ℕ) : ZMod 2006) ∈ fanChord k' := by
    rw [← hh, fanChord]; simp
  rw [fanChord, Finset.mem_insert, Finset.mem_singleton] at h1
  have hb := k.2; have hb' := k'.2
  rcases h1 with h1 | h1
  · exfalso
    have g := congrArg ZMod.val h1
    rw [ZMod.val_natCast, ZMod.val_zero] at g
    omega
  · have g := congrArg ZMod.val h1
    rw [ZMod.val_natCast, ZMod.val_natCast] at g
    have hkv : k.val = k'.val := by omega
    exact Fin.ext hkv

lemma not_earChord_eq_fanChord {i : Fin 1003} {k : Fin 1000} : earChord i ≠ fanChord k := by
  intro hh
  have h1 : ((2 * i.val : ℕ) : ZMod 2006) ∈ fanChord k := by
    rw [← hh, earChord]; simp
  rw [fanChord, Finset.mem_insert, Finset.mem_singleton] at h1
  have hb := i.2; have hbk := k.2
  rcases h1 with h1 | h1
  · -- ↑(2i) = 0 → 2i ≡ 0 (mod 2006) → i = 0; then ↑(2i+2) = ↑2 ∈ fanChord k
    have g := congrArg ZMod.val h1
    rw [ZMod.val_natCast, ZMod.val_zero] at g
    have hi0 : 2 * i.val % 2006 = 0 := by omega
    have h2 : ((2 * i.val + 2 : ℕ) : ZMod 2006) ∈ fanChord k := by
      rw [← hh, earChord]; simp
    rw [fanChord, Finset.mem_insert, Finset.mem_singleton] at h2
    rcases h2 with h2 | h2
    · have g2 := congrArg ZMod.val h2
      rw [ZMod.val_natCast, show (0 : ZMod 2006).val = 0 from ZMod.val_zero] at g2
      omega
    · have g2 := congrArg ZMod.val h2
      rw [ZMod.val_natCast, ZMod.val_natCast] at g2
      omega
  · -- ↑(2i) = ↑(2k+4) and then ↑(2i+2) = 0 → 2i+2 ≡ 0 → i = 1002 → 2k+4 ≡ 2004 ✗
    have h2 : ((2 * i.val + 2 : ℕ) : ZMod 2006) ∈ fanChord k := by
      rw [← hh, earChord]; simp
    rw [fanChord, Finset.mem_insert, Finset.mem_singleton] at h2
    rcases h2 with h2 | h2
    · have g := congrArg ZMod.val h1
      rw [ZMod.val_natCast, ZMod.val_natCast] at g
      have g2 := congrArg ZMod.val h2
      rw [ZMod.val_natCast, show (0 : ZMod 2006).val = 0 from ZMod.val_zero] at g2
      omega
    · have g := congrArg ZMod.val h1
      rw [ZMod.val_natCast, ZMod.val_natCast] at g
      have g2 := congrArg ZMod.val h2
      rw [ZMod.val_natCast, ZMod.val_natCast] at g2
      omega

lemma val_add_one (i : ZMod 2006) : (i + 1).val = (i.val + 1) % 2006 := by
  have h : (i + 1 : ZMod 2006) = ((i.val + 1 : ℕ) : ZMod 2006) := by
    rw [Nat.cast_add, ZMod.natCast_zmod_val, show (1 : ZMod 2006) = ((1 : ℕ) : ZMod 2006) from by norm_num]
  rw [h, ZMod.val_natCast]

lemma not_arc_one_even {x y : ZMod 2006} (hx : x.val % 2 = 0) (hy : y.val % 2 = 0) :
    arc x y ≠ 1 := by
  intro h
  have h2 : (y - x).val = 1 := h
  rcases le_total x.val y.val with hle | hle
  · have h3 := ZMod.val_sub (n := 2006) (a := y) (b := x) hle
    omega
  · have h4 : (x - y).val = x.val - y.val := ZMod.val_sub (n := 2006) (a := x) (b := y) hle
    have hne : x - y ≠ 0 := by
      intro hh
      have hh2 : x = y := sub_eq_zero.mp hh
      rw [hh2, sub_self] at h2
      simp at h2
    haveI : NeZero (x - y) := ⟨hne⟩
    have h6 : (y - x) = -(x - y) := by abel
    have h5 : (y - x).val = 2006 - (x - y).val := by rw [h6, ZMod.val_neg_of_ne_zero]
    omega

lemma not_side_in_cenTri (j : Fin 1001) (i : ZMod 2006) :
    ¬ (({i, i + 1} : Finset (ZMod 2006)) ⊆ cenTri j) := by
  intro hsub
  have hi : i ∈ cenTri j := hsub (by simp)
  have hi1 : i + 1 ∈ cenTri j := hsub (by simp)
  rw [cenTri, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hi hi1
  have h0 : (0 : ZMod 2006).val % 2 = 0 := by rw [ZMod.val_zero]
  have h2j : ((2 * j.val + 2 : ℕ) : ZMod 2006).val % 2 = 0 := by rw [val_parity_natCast]; omega
  have h4j : ((2 * j.val + 4 : ℕ) : ZMod 2006).val % 2 = 0 := by rw [val_parity_natCast]; omega
  rcases hi with rfl | rfl | rfl <;> rcases hi1 with h1 | h1 | h1
  · -- i = 0, i+1 = 0: (0+1).val = 1 ≠ 0
    have g := congrArg ZMod.val h1
    rw [val_add_one, ZMod.val_zero] at g
    omega
  · -- i = 0, i+1 = ↑(2j+2): arc = 2j+2 ≠ 1
    have h3 : arc 0 ((2 * j.val + 2 : ℕ) : ZMod 2006) = 1 := h1 ▸ arc_side 0
    exact not_arc_one_even h0 h2j h3
  · -- i = 0, i+1 = ↑(2j+4)
    have h3 : arc 0 ((2 * j.val + 4 : ℕ) : ZMod 2006) = 1 := h1 ▸ arc_side 0
    exact not_arc_one_even h0 h4j h3
  · -- i = ↑(2j+2), i+1 = 0
    have h3 : arc ((2 * j.val + 2 : ℕ) : ZMod 2006) 0 = 1 := h1 ▸ arc_side _
    exact not_arc_one_even h2j h0 h3
  · -- i = ↑(2j+2), i+1 = ↑(2j+2): x+1 = x
    exfalso
    have g : (1 : ZMod 2006) = 0 := by linear_combination h1
    exact one_ne_zero_zmod g
  · -- i = ↑(2j+2), i+1 = ↑(2j+4)
    have h3 : arc ((2 * j.val + 2 : ℕ) : ZMod 2006) ((2 * j.val + 4 : ℕ) : ZMod 2006) = 1 :=
      h1 ▸ arc_side _
    exact not_arc_one_even h2j h4j h3
  · -- i = ↑(2j+4), i+1 = 0
    have h3 : arc ((2 * j.val + 4 : ℕ) : ZMod 2006) 0 = 1 := h1 ▸ arc_side _
    exact not_arc_one_even h4j h0 h3
  · -- i = ↑(2j+4), i+1 = ↑(2j+2)
    have h3 : arc ((2 * j.val + 4 : ℕ) : ZMod 2006) ((2 * j.val + 2 : ℕ) : ZMod 2006) = 1 :=
      h1 ▸ arc_side _
    exact not_arc_one_even h4j h2j h3
  · -- i = ↑(2j+4), i+1 = ↑(2j+4)
    exfalso
    have g : (1 : ZMod 2006) = 0 := by linear_combination h1
    exact one_ne_zero_zmod g

lemma side_container_unique {i : ZMod 2006} {i' : Fin 1003}
    (hsub : ({i, i + 1} : Finset (ZMod 2006)) ⊆ earTri i') :
    (i = ((2 * i'.val : ℕ) : ZMod 2006) ∧ i.val % 2 = 0) ∨
    (i = ((2 * i'.val + 1 : ℕ) : ZMod 2006) ∧ i.val % 2 = 1) := by
  have hi : i ∈ earTri i' := hsub (by simp)
  have hi1 : i + 1 ∈ earTri i' := hsub (by simp)
  rw [earTri, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hi hi1
  have hb := i'.2
  rcases hi with rfl | rfl | rfl <;> rcases hi1 with h1 | h1 | h1
  · -- i = ↑(2i'), i+1 = ↑(2i'): contradiction x+1 = x
    exfalso
    have g : (1 : ZMod 2006) = 0 := by linear_combination h1
    exact one_ne_zero_zmod g
  · -- i = ↑(2i'), i+1 = ↑(2i'+1) ✓ even case
    left
    exact ⟨rfl, by rw [ZMod.val_natCast]; omega⟩
  · -- i = ↑(2i'), i+1 = ↑(2i'+2): arc = 2 ≠ 1
    have h3 : arc ((2 * i'.val : ℕ) : ZMod 2006) ((2 * i'.val + 2 : ℕ) : ZMod 2006) = 1 :=
      h1 ▸ arc_side _
    have h02 := arc_earChord i'
    omega
  · -- i = ↑(2i'+1), i+1 = ↑(2i'): arc = 2005 ≠ 1
    have h3 : arc ((2 * i'.val + 1 : ℕ) : ZMod 2006) ((2 * i'.val : ℕ) : ZMod 2006) = 1 :=
      h1 ▸ arc_side _
    have h01 : arc ((2 * i'.val : ℕ) : ZMod 2006) ((2 * i'.val + 1 : ℕ) : ZMod 2006) = 1 := by
      rw [arc_ofNat_le (by omega) (by omega)]
      omega
    have hadd := arc_add_arc (earTri_ne i').1
    omega
  · -- i = ↑(2i'+1), i+1 = ↑(2i'+1): contradiction
    exfalso
    have g : (1 : ZMod 2006) = 0 := by linear_combination h1
    exact one_ne_zero_zmod g
  · -- i = ↑(2i'+1), i+1 = ↑(2i'+2) ✓ odd case
    right
    exact ⟨rfl, by rw [ZMod.val_natCast]; omega⟩
  · -- i = ↑(2i'+2), i+1 = ↑(2i'): arc = 2004 ≠ 1
    have h3 : arc ((2 * i'.val + 2 : ℕ) : ZMod 2006) ((2 * i'.val : ℕ) : ZMod 2006) = 1 :=
      h1 ▸ arc_side _
    have h02 := arc_earChord i'
    have hadd := arc_add_arc (earTri_ne i').2.1
    omega
  · -- i = ↑(2i'+2), i+1 = ↑(2i'+1): arc = 2005 ≠ 1
    have h3 : arc ((2 * i'.val + 2 : ℕ) : ZMod 2006) ((2 * i'.val + 1 : ℕ) : ZMod 2006) = 1 :=
      h1 ▸ arc_side _
    have h12 : arc ((2 * i'.val + 1 : ℕ) : ZMod 2006) ((2 * i'.val + 2 : ℕ) : ZMod 2006) = 1 := by
      rw [arc_ofNat_le (by omega) (by omega)]
      omega
    have hadd := arc_add_arc (earTri_ne i').2.2
    omega
  · -- i = ↑(2i'+2), i+1 = ↑(2i'+2): contradiction
    exfalso
    have g : (1 : ZMod 2006) = 0 := by linear_combination h1
    exact one_ne_zero_zmod g

theorem side_exactly_one (i : ZMod 2006) :
    (D₀.filter fun T => ({i, i + 1} : Finset (ZMod 2006)) ⊆ T).card = 1 := by
  have hii : i = ((i.val : ℕ) : ZMod 2006) := (ZMod.natCast_zmod_val i).symm
  have hlt := ZMod.val_lt i
  by_cases hpar : i.val % 2 = 0
  · have hbt : i.val / 2 < 1003 := by omega
    refine Finset.card_eq_one.mpr ⟨earTri ⟨i.val / 2, hbt⟩, ?_⟩
    ext T
    simp only [D₀, Finset.mem_filter, Finset.mem_union, Finset.mem_image, Finset.mem_singleton]
    constructor
    · rintro ⟨hT, hsub⟩
      rcases hT with ⟨i', -, rfl⟩ | ⟨j', -, rfl⟩
      · have hu := side_container_unique hsub
        rcases hu with ⟨hi, hpar'⟩ | ⟨hi, hpar'⟩
        · have h1 : i.val = 2 * i'.val := by
            have g := congrArg ZMod.val hi
            rw [ZMod.val_natCast] at g
            omega
          have h2 : i' = ⟨i.val / 2, hbt⟩ := by
            apply Fin.ext
            show i'.val = i.val / 2
            omega
          rw [h2]
        · exfalso
          have g := congrArg ZMod.val hi
          rw [ZMod.val_natCast] at g
          omega
      · exfalso
        exact not_side_in_cenTri j' i hsub
    · intro hT
      rw [hT]
      refine ⟨Or.inl ⟨⟨i.val / 2, hbt⟩, Finset.mem_univ _, rfl⟩, ?_⟩
      have e : earTri ⟨i.val / 2, hbt⟩ = {((2 * (i.val / 2) : ℕ) : ZMod 2006),
          ((2 * (i.val / 2) + 1 : ℕ) : ZMod 2006), ((2 * (i.val / 2) + 2 : ℕ) : ZMod 2006)} := by
        show earTri ⟨i.val / 2, hbt⟩ = _
        rfl
      intro x hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rw [e, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]
      have h1 : i = ((2 * (i.val / 2) : ℕ) : ZMod 2006) := by
        have e1 : (2 * (i.val / 2) : ℕ) = i.val := by omega
        rw [e1]
        exact hii
      have h2 : i + 1 = ((2 * (i.val / 2) + 1 : ℕ) : ZMod 2006) := by
        have e2 : (2 * (i.val / 2) + 1 : ℕ) = i.val + 1 := by omega
        have h0 : (i + 1 : ZMod 2006) = ((i.val + 1 : ℕ) : ZMod 2006) := by
          rw [Nat.cast_add, ZMod.natCast_zmod_val,
            show (1 : ZMod 2006) = ((1 : ℕ) : ZMod 2006) from by norm_num]
        rw [h0, e2]
      rcases hx with rfl | rfl
      · exact Or.inl h1
      · exact Or.inr (Or.inl h2)
  · have hpar1 : i.val % 2 = 1 := by omega
    have hbt : (i.val - 1) / 2 < 1003 := by omega
    refine Finset.card_eq_one.mpr ⟨earTri ⟨(i.val - 1) / 2, hbt⟩, ?_⟩
    ext T
    simp only [D₀, Finset.mem_filter, Finset.mem_union, Finset.mem_image, Finset.mem_singleton]
    constructor
    · rintro ⟨hT, hsub⟩
      rcases hT with ⟨i', -, rfl⟩ | ⟨j', -, rfl⟩
      · have hu := side_container_unique hsub
        rcases hu with ⟨hi, hpar'⟩ | ⟨hi, hpar'⟩
        · exfalso
          have g := congrArg ZMod.val hi
          rw [ZMod.val_natCast] at g
          omega
        · have h1 : i.val = 2 * i'.val + 1 := by
            have g := congrArg ZMod.val hi
            rw [ZMod.val_natCast] at g
            omega
          have h2 : i' = ⟨(i.val - 1) / 2, hbt⟩ := by
            apply Fin.ext
            show i'.val = (i.val - 1) / 2
            omega
          rw [h2]
      · exfalso
        exact not_side_in_cenTri j' i hsub
    · intro hT
      rw [hT]
      refine ⟨Or.inl ⟨⟨(i.val - 1) / 2, hbt⟩, Finset.mem_univ _, rfl⟩, ?_⟩
      have e : earTri ⟨(i.val - 1) / 2, hbt⟩ = {((2 * ((i.val - 1) / 2) : ℕ) : ZMod 2006),
          ((2 * ((i.val - 1) / 2) + 1 : ℕ) : ZMod 2006),
          ((2 * ((i.val - 1) / 2) + 2 : ℕ) : ZMod 2006)} := by
        show earTri ⟨(i.val - 1) / 2, hbt⟩ = _
        rfl
      intro x hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rw [e, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]
      have h1 : i = ((2 * ((i.val - 1) / 2) + 1 : ℕ) : ZMod 2006) := by
        have e1 : (2 * ((i.val - 1) / 2) + 1 : ℕ) = i.val := by omega
        rw [e1]
        exact hii
      have h2 : i + 1 = ((2 * ((i.val - 1) / 2) + 2 : ℕ) : ZMod 2006) := by
        have e2 : (2 * ((i.val - 1) / 2) + 2 : ℕ) = i.val + 1 := by omega
        have h0 : (i + 1 : ZMod 2006) = ((i.val + 1 : ℕ) : ZMod 2006) := by
          rw [Nat.cast_add, ZMod.natCast_zmod_val,
            show (1 : ZMod 2006) = ((1 : ℕ) : ZMod 2006) from by norm_num]
        rw [h0, e2]
      rcases hx with rfl | rfl
      · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inr h2)

lemma card_diags_D₀ : (diags D₀).card = 2003 := by
  have hdisj : Disjoint (Finset.univ.image earChord) (Finset.univ.image fanChord) := by
    rw [Finset.disjoint_left]
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨i, -, rfl⟩ := hx
    rw [Finset.mem_image]
    intro hxc
    obtain ⟨k, -, hkk⟩ := hxc
    exact not_earChord_eq_fanChord hkk.symm
  rw [diags_D₀]
  show (Finset.univ.image earChord ∪ Finset.univ.image fanChord).card = 2003
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ earChord_injective,
    Finset.card_image_of_injective _ fanChord_injective, Finset.card_univ, Finset.card_univ,
    Fintype.card_fin, Fintype.card_fin]

lemma earChord_in_earTri {i : Fin 1003} {i' : Fin 1003} (hsub : earChord i ⊆ earTri i') :
    i' = i := by
  have h1 : ((2 * i.val : ℕ) : ZMod 2006) ∈ earTri i' := hsub (by simp [earChord])
  rw [earTri, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at h1
  have hb := i.2; have hb' := i'.2
  rcases h1 with h1 | h1 | h1
  · have g := congrArg ZMod.val h1
    rw [ZMod.val_natCast, ZMod.val_natCast] at g
    have hiv : i'.val = i.val := by omega
    exact Fin.ext hiv
  · exfalso
    have g := congrArg (fun x : ZMod 2006 => x.val % 2) h1
    rw [val_parity_natCast, val_parity_natCast] at g
    omega
  · -- ↑(2i) = ↑(2i'+2): use second element
    have h2 : ((2 * i.val + 2 : ℕ) : ZMod 2006) ∈ earTri i' := hsub (by simp [earChord])
    rw [earTri, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at h2
    rcases h2 with h2 | h2 | h2
    · exfalso
      have g := congrArg ZMod.val h1
      rw [ZMod.val_natCast, ZMod.val_natCast] at g
      have g2 := congrArg ZMod.val h2
      rw [ZMod.val_natCast, ZMod.val_natCast] at g2
      omega
    · exfalso
      have g := congrArg (fun x : ZMod 2006 => x.val % 2) h2
      rw [val_parity_natCast, val_parity_natCast] at g
      omega
    · exfalso
      have g := congrArg ZMod.val h1
      rw [ZMod.val_natCast, ZMod.val_natCast] at g
      have g2 := congrArg ZMod.val h2
      rw [ZMod.val_natCast, ZMod.val_natCast] at g2
      omega

lemma earChord_in_cenTri {i : Fin 1003} {j' : Fin 1001} (hsub : earChord i ⊆ cenTri j') :
    (i.val = 0 ∧ j'.val = 0) ∨ (1 ≤ i.val ∧ i.val ≤ 1001 ∧ j'.val = i.val - 1) ∨
    (i.val = 1002 ∧ j'.val = 1000) := by
  have h1 : ((2 * i.val : ℕ) : ZMod 2006) ∈ cenTri j' := hsub (by simp [earChord])
  rw [cenTri, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at h1
  have hb := i.2; have hb' := j'.2
  rcases h1 with h1 | h1 | h1
  · -- ↑(2i) = 0 → i = 0; then ↑2 ∈ cenTri j' → j' = 0
    have g := congrArg ZMod.val h1
    rw [ZMod.val_natCast, ZMod.val_zero] at g
    have hi0 : i.val = 0 := by omega
    left
    refine ⟨hi0, ?_⟩
    have h2 : ((2 * i.val + 2 : ℕ) : ZMod 2006) ∈ cenTri j' := hsub (by simp [earChord])
    rw [hi0] at h2
    rw [cenTri, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at h2
    have e : ((2 * 0 + 2 : ℕ) : ZMod 2006) = ((2 : ℕ) : ZMod 2006) := by norm_num
    rw [e] at h2
    rcases h2 with h2 | h2 | h2
    · exfalso
      have g2 := congrArg ZMod.val h2
      rw [ZMod.val_natCast, show (0 : ZMod 2006).val = 0 from ZMod.val_zero] at g2
      omega
    · have g2 := congrArg ZMod.val h2
      rw [ZMod.val_natCast, ZMod.val_natCast] at g2
      omega
    · exfalso
      have g2 := congrArg ZMod.val h2
      rw [ZMod.val_natCast, ZMod.val_natCast] at g2
      omega
  · -- ↑(2i) = ↑(2j'+2) → i = j'+1; then ↑(2i+2) must be ↑(2j'+4)
    have g := congrArg ZMod.val h1
    rw [ZMod.val_natCast, ZMod.val_natCast] at g
    have hij : i.val = j'.val + 1 := by omega
    right; left
    refine ⟨by omega, by omega, by omega⟩
  · -- ↑(2i) = ↑(2j'+4) → i = j'+2; then ↑(2i+2) = 0 forces i = 1002, j' = 1000
    have g := congrArg ZMod.val h1
    rw [ZMod.val_natCast, ZMod.val_natCast] at g
    have hij : i.val = j'.val + 2 := by omega
    have h2 : ((2 * i.val + 2 : ℕ) : ZMod 2006) ∈ cenTri j' := hsub (by simp [earChord])
    rw [cenTri, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at h2
    rcases h2 with h2 | h2 | h2
    · -- ↑(2i+2) = 0
      have g2 := congrArg ZMod.val h2
      rw [ZMod.val_natCast, show (0 : ZMod 2006).val = 0 from ZMod.val_zero] at g2
      right; right
      refine ⟨by omega, by omega⟩
    · exfalso
      have g2 := congrArg ZMod.val h2
      rw [ZMod.val_natCast, ZMod.val_natCast] at g2
      omega
    · exfalso
      have g2 := congrArg ZMod.val h2
      rw [ZMod.val_natCast, ZMod.val_natCast] at g2
      omega

lemma fanChord_not_in_earTri {k : Fin 1000} {i' : Fin 1003} : ¬ (fanChord k ⊆ earTri i') := by
  intro hsub
  have h1 : (0 : ZMod 2006) ∈ earTri i' := hsub (by simp [fanChord])
  rw [earTri, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at h1
  have hb := i'.2; have hbk := k.2
  rcases h1 with h1 | h1 | h1
  · -- 0 = ↑(2i') → i'.val = 0; then ↑(2k+4) ∈ earTri i' impossible
    have g := congrArg ZMod.val h1
    rw [ZMod.val_zero, ZMod.val_natCast] at g
    have hi0 : i'.val = 0 := by omega
    have h2 : ((2 * k.val + 4 : ℕ) : ZMod 2006) ∈ earTri i' := hsub (by simp [fanChord])
    rw [earTri, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at h2
    rcases h2 with h2 | h2 | h2
    · exfalso
      have g2 := congrArg ZMod.val h2
      rw [ZMod.val_natCast, ZMod.val_natCast] at g2
      omega
    · exfalso
      have g2 := congrArg ZMod.val h2
      rw [ZMod.val_natCast, ZMod.val_natCast] at g2
      omega
    · exfalso
      have g2 := congrArg ZMod.val h2
      rw [ZMod.val_natCast, ZMod.val_natCast] at g2
      omega
  · -- 0 = ↑(2i'+1): odd val can't be 0
    exfalso
    have g := congrArg ZMod.val h1
    rw [ZMod.val_zero, ZMod.val_natCast] at g
    omega
  · -- 0 = ↑(2i'+2) → i'.val = 1002; then ↑(2k+4) ∈ earTri i' impossible
    have g := congrArg ZMod.val h1
    rw [ZMod.val_zero, ZMod.val_natCast] at g
    have hi : i'.val = 1002 := by omega
    have h2 : ((2 * k.val + 4 : ℕ) : ZMod 2006) ∈ earTri i' := hsub (by simp [fanChord])
    rw [earTri, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at h2
    rcases h2 with h2 | h2 | h2
    · exfalso
      have g2 := congrArg ZMod.val h2
      rw [ZMod.val_natCast, ZMod.val_natCast, hi] at g2
      omega
    · exfalso
      have g2 := congrArg (fun x : ZMod 2006 => x.val % 2) h2
      rw [val_parity_natCast, val_parity_natCast, hi] at g2
      omega
    · exfalso
      have g2 := congrArg ZMod.val h2
      rw [ZMod.val_natCast, ZMod.val_natCast] at g2
      omega

lemma fanChord_in_cenTri {k : Fin 1000} {j' : Fin 1001} (hsub : fanChord k ⊆ cenTri j') :
    j'.val = k.val ∨ j'.val = k.val + 1 := by
  have h1 : ((2 * k.val + 4 : ℕ) : ZMod 2006) ∈ cenTri j' := hsub (by simp [fanChord])
  rw [cenTri, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at h1
  have hbk := k.2; have hb' := j'.2
  rcases h1 with h1 | h1 | h1
  · exfalso
    have g := congrArg ZMod.val h1
    rw [ZMod.val_natCast, ZMod.val_zero] at g
    omega
  · have g := congrArg ZMod.val h1
    rw [ZMod.val_natCast, ZMod.val_natCast] at g
    right
    omega
  · have g := congrArg ZMod.val h1
    rw [ZMod.val_natCast, ZMod.val_natCast] at g
    left
    omega

lemma containers_earChord (i : Fin 1003) :
    ∃ j : Fin 1001, (D₀.filter (earChord i ⊆ ·)) = {earTri i, cenTri j} := by
  by_cases hi0 : i.val = 0
  · refine ⟨⟨0, by omega⟩, ?_⟩
    ext T
    simp only [D₀, Finset.mem_filter, Finset.mem_union, Finset.mem_image, Finset.mem_singleton,
      Finset.mem_insert]
    constructor
    · rintro ⟨hT, hsub⟩
      rcases hT with ⟨i', -, rfl⟩ | ⟨j', -, rfl⟩
      · rw [earChord_in_earTri hsub]
        simp
      · have hj := earChord_in_cenTri hsub
        rcases hj with ⟨-, hj0'⟩ | ⟨h1le, -, -⟩ | ⟨h1002, -⟩
        · exact Or.inr (congrArg cenTri (Fin.ext hj0' : j' = ⟨0, by omega⟩))
        · omega
        · omega
    · rintro (rfl | rfl)
      · refine ⟨Or.inl ⟨i, Finset.mem_univ _, rfl⟩, ?_⟩
        intro x hx
        simp only [earChord, Finset.mem_insert, Finset.mem_singleton] at hx
        rw [earTri, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]
        rcases hx with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (Or.inr rfl)
      · refine ⟨Or.inr ⟨⟨0, by omega⟩, Finset.mem_univ _, rfl⟩, ?_⟩
        intro x hx
        simp only [earChord, Finset.mem_insert, Finset.mem_singleton] at hx
        rw [cenTri, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]
        rcases hx with rfl | rfl
        · have e : ((2 * i.val : ℕ) : ZMod 2006) = 0 := by
            rw [hi0]; decide
          rw [e]
          exact Or.inl rfl
        · have e : ((2 * i.val + 2 : ℕ) : ZMod 2006) = ((2 : ℕ) : ZMod 2006) := by
            rw [hi0]
          rw [e]
          exact Or.inr (Or.inl rfl)
  · by_cases hi1002 : i.val = 1002
    · refine ⟨1000, ?_⟩
      ext T
      simp only [D₀, Finset.mem_filter, Finset.mem_union, Finset.mem_image, Finset.mem_singleton,
        Finset.mem_insert]
      constructor
      · rintro ⟨hT, hsub⟩
        rcases hT with ⟨i', -, rfl⟩ | ⟨j', -, rfl⟩
        · rw [earChord_in_earTri hsub]
          simp
        · have hj := earChord_in_cenTri hsub
          rcases hj with ⟨hi0c, -⟩ | ⟨h1le, h1ge, -⟩ | ⟨-, hj'⟩
          · omega
          · omega
          · exact Or.inr (congrArg cenTri (Fin.ext hj' : j' = ⟨1000, by omega⟩))
      · rintro (rfl | rfl)
        · refine ⟨Or.inl ⟨i, Finset.mem_univ _, rfl⟩, ?_⟩
          intro x hx
          simp only [earChord, Finset.mem_insert, Finset.mem_singleton] at hx
          rw [earTri, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]
          rcases hx with rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr (Or.inr rfl)
        · refine ⟨Or.inr ⟨⟨1000, by omega⟩, Finset.mem_univ _, rfl⟩, ?_⟩
          intro x hx
          simp only [earChord, Finset.mem_insert, Finset.mem_singleton] at hx
          rw [cenTri, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]
          rcases hx with rfl | rfl
          · have e : ((2 * i.val : ℕ) : ZMod 2006) = ((2004 : ℕ) : ZMod 2006) := by
              rw [hi1002]
            rw [e]
            exact Or.inr (Or.inr rfl)
          · have e : ((2 * i.val + 2 : ℕ) : ZMod 2006) = 0 := by
              rw [hi1002]; decide
            rw [e]
            exact Or.inl rfl
    · have hbi : 1 ≤ i.val ∧ i.val ≤ 1001 := by
        have := i.2
        omega
      refine ⟨⟨i.val - 1, by omega⟩, ?_⟩
      ext T
      simp only [D₀, Finset.mem_filter, Finset.mem_union, Finset.mem_image, Finset.mem_singleton,
        Finset.mem_insert]
      constructor
      · rintro ⟨hT, hsub⟩
        rcases hT with ⟨i', -, rfl⟩ | ⟨j', -, rfl⟩
        · rw [earChord_in_earTri hsub]
          simp
        · have hj := earChord_in_cenTri hsub
          rcases hj with ⟨hi0', -⟩ | ⟨h1le, h1ge, hj'⟩ | ⟨hi1002', -⟩
          · omega
          · exact Or.inr (congrArg cenTri (Fin.ext hj' : j' = ⟨i.val - 1, by omega⟩))
          · omega
      · rintro (rfl | rfl)
        · refine ⟨Or.inl ⟨i, Finset.mem_univ _, rfl⟩, ?_⟩
          intro x hx
          simp only [earChord, Finset.mem_insert, Finset.mem_singleton] at hx
          rw [earTri]
          simp only [Finset.mem_insert, Finset.mem_singleton]
          rcases hx with rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr (Or.inr rfl)
        · refine ⟨Or.inr ⟨⟨i.val - 1, by omega⟩, Finset.mem_univ _, rfl⟩, ?_⟩
          intro x hx
          simp only [earChord, Finset.mem_insert, Finset.mem_singleton] at hx
          rw [cenTri]
          simp only [Finset.mem_insert, Finset.mem_singleton]
          have e1 : ((2 * (i.val - 1) + 2 : ℕ) : ZMod 2006) = ((2 * i.val : ℕ) : ZMod 2006) := by
            have e : (2 * (i.val - 1) + 2 : ℕ) = 2 * i.val := by omega
            rw [e]
          have e2 : ((2 * (i.val - 1) + 4 : ℕ) : ZMod 2006) = ((2 * i.val + 2 : ℕ) : ZMod 2006) := by
            have e : (2 * (i.val - 1) + 4 : ℕ) = 2 * i.val + 2 := by omega
            rw [e]
          rcases hx with rfl | rfl
          · rw [e1]
            exact Or.inr (Or.inl rfl)
          · rw [e2]
            exact Or.inr (Or.inr rfl)

lemma containers_fanChord (k : Fin 1000) :
    (D₀.filter (fanChord k ⊆ ·)) =
      {cenTri ⟨k.val, by have := k.2; omega⟩, cenTri ⟨k.val + 1, by have := k.2; omega⟩} := by
  ext T
  simp only [D₀, Finset.mem_filter, Finset.mem_union, Finset.mem_image, Finset.mem_singleton,
    Finset.mem_insert]
  constructor
  · rintro ⟨hT, hsub⟩
    rcases hT with ⟨i', -, rfl⟩ | ⟨j', -, rfl⟩
    · exact absurd hsub fanChord_not_in_earTri
    · have hj := fanChord_in_cenTri hsub
      rcases hj with hj' | hj'
      · left
        have : j' = ⟨k.val, by have := k.2; omega⟩ := Fin.ext hj'
        rw [this]
      · right
        have : j' = ⟨k.val + 1, by have := k.2; omega⟩ := Fin.ext hj'
        rw [this]
  · rintro (rfl | rfl)
    · refine ⟨Or.inr ⟨⟨k.val, by have := k.2; omega⟩, Finset.mem_univ _, rfl⟩, ?_⟩
      intro x hx
      simp only [fanChord, Finset.mem_insert, Finset.mem_singleton] at hx
      rw [cenTri]
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases hx with rfl | rfl
      · left; rfl
      · right; right; rfl
    · refine ⟨Or.inr ⟨⟨k.val + 1, by have := k.2; omega⟩, Finset.mem_univ _, rfl⟩, ?_⟩
      intro x hx
      simp only [fanChord, Finset.mem_insert, Finset.mem_singleton] at hx
      rw [cenTri]
      simp only [Finset.mem_insert, Finset.mem_singleton]
      have e : ((2 * (k.val + 1) + 2 : ℕ) : ZMod 2006) = ((2 * k.val + 4 : ℕ) : ZMod 2006) := by
        have e2 : (2 * (k.val + 1) + 2 : ℕ) = 2 * k.val + 4 := by omega
        rw [e2]
      rcases hx with rfl | rfl
      · left; rfl
      · rw [e]; right; left; rfl

set_option maxRecDepth 8192 in
set_option linter.constructorNameAsVariable false in
theorem diag_exactly_two (T : Finset (ZMod 2006)) (hT : T ∈ D₀) (p : Finset (ZMod 2006))
    (hp : p ∈ T.powersetCard 2) (hdiag : IsDiag p) :
    (D₀.filter fun T' => p ⊆ T').card = 2 := by
  have hpd : p ∈ diags D₀ := by
    simp only [diags, Finset.mem_biUnion]
    exact ⟨T, hT, Finset.mem_filter.mpr ⟨hp, hdiag⟩⟩
  rw [diags_D₀, Finset.mem_union, Finset.mem_image, Finset.mem_image] at hpd
  rcases hpd with ⟨i, -, rfl⟩ | ⟨k, -, rfl⟩
  · obtain ⟨j, hj⟩ := containers_earChord i
    rw [hj, Finset.card_eq_two.mpr ⟨earTri i, cenTri j, not_earTri_eq_cenTri, rfl⟩]
  · have hb1 : k.val < 1001 := by have := k.2; omega
    have hb2 : k.val + 1 < 1001 := by have := k.2; omega
    have hne : cenTri ⟨k.val, hb1⟩ ≠ cenTri ⟨k.val + 1, hb2⟩ := by
      intro hh
      have h2 := cenTri_injective hh
      have hv := congrArg Fin.val h2
      simp at hv
    rw [containers_fanChord k]
    exact Finset.card_eq_two.mpr ⟨cenTri ⟨k.val, hb1⟩, cenTri ⟨k.val + 1, hb2⟩, hne, rfl⟩

theorem construction_special : (D₀.filter IsSpecial).card = 1003 := by
  rw [filter_special_D₀, Finset.card_image_of_injective _ earTri_injective, Finset.card_univ,
    Fintype.card_fin]

end noncross_manual

theorem construction : IsDissection D₀ ∧ (D₀.filter IsSpecial).card = 1003 := by
  have h4 : (∀ T ∈ D₀, ∀ p ∈ T.powersetCard 2, IsDiag p →
      (D₀.filter fun T' => p ⊆ T').card = 2) :=
    fun T hT p hp hdiag => diag_exactly_two T hT p hp hdiag
  have h5 : noncrossPred (diags D₀) := construction_noncross
  have h3 : (∀ i : ZMod 2006,
      (D₀.filter fun T => ({i, i + 1} : Finset (ZMod 2006)) ⊆ T).card = 1) :=
    fun i => side_exactly_one i
  exact ⟨⟨card3_mem_D₀, card_D₀, h3, h4, h5, card_diags_D₀⟩, construction_special⟩

end construction

determine answer : ℕ := 1003

problem imo2006_p2 :
    IsGreatest {n : ℕ | ∃ D : Finset (Finset (ZMod 2006)), IsDissection D ∧
      (D.filter IsSpecial).card = n} answer := by
  constructor
  · exact ⟨D₀, construction.1, construction.2⟩
  · intro n hn
    obtain ⟨D, hD, rfl⟩ := hn
    exact upper_bound hD

end Imo2006P2

/- PROGRESS NOTES (for the next resume):
Architecture: upper bound fully proved (arc API in ZMod 2006, parity, double
counting sum_ng_eq, charging injection shortTri, upper_bound). Construction D₀
(ears + central fan) is verified fieldwise: h5 (non-crossing) is proved MANUALLY
(section noncross_manual: parity kill for ear chords, cross_comm, fan-fan value
arithmetic), h7 (exactly the 1003 ears are special) is proved manually, and the
remaining small ZMod 2006 computations use `decide` (kernel reduction, no extra
axioms); no `native_decide` remains anywhere in the file.
IMPORTANT: `native_decide` on the original full conjunction was killed (RC=137)
because the cgroup memory limit is 32 GB and each native_decide accumulates
several GB of compiled evaluation code; the 2003 x 2003 `Cross` decidability
evaluation alone ballooned past 22 GB. Keep the number of native_decide calls
minimal; anything heavier than ~4M subset checks should be proved by hand.
-/
