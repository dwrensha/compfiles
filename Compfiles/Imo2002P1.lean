/-
Copyright (c) 2026 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Olympiad 2002, Problem 1

Let n be a positive integer. Let T be the set of points (x, y) in the
plane where x and y are non-negative integers and x + y < n. Each
point of T is coloured red or blue, subject to the following
condition: if a point (x, y) is red, then so are all points (x', y')
of T with x' ≤ x and y' ≤ y. Let A be the number of ways of choosing
n blue points with distinct x-coordinates, and let B be the number of
ways of choosing n blue points with distinct y-coordinates. Prove
that A = B.
-/

namespace Imo2002P1

inductive Color : Type where
| red : Color
| blue : Color
deriving DecidableEq, Fintype

/-- The points (x, y) with nonnegative integer coordinates and x + y < n. -/
def T (n : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range n ×ˢ Finset.range n).filter fun p ↦ p.1 + p.2 < n

/-- The sets of n blue points in T whose coordinates are distinct in
the dimension selected by `coord`. -/
def ChoiceCount (n : ℕ) (color : ℕ × ℕ → Color) (coord : ℕ × ℕ → ℕ) : ℕ :=
  (((T n).powersetCard n).filter fun s ↦
    (∀ p ∈ s, color p = .blue) ∧
    ∀ p ∈ s, ∀ q ∈ s, coord p = coord q → p = q).card

snip begin

lemma color_eq_blue_iff (c : Color) : c = .blue ↔ ¬ c = .red := by
  cases c <;> simp

/-- A downward-closed finite set of naturals is an initial segment. -/
lemma downward_closed_iff_lt_card {S : Finset ℕ}
    (h : ∀ a b, a ≤ b → b ∈ S → a ∈ S) (y : ℕ) : y ∈ S ↔ y < S.card := by
  constructor
  · intro hy
    have h1 : Finset.range (y + 1) ⊆ S := by
      intro a ha
      rw [Finset.mem_range] at ha
      exact h a y (by lia) hy
    have h2 := Finset.card_le_card h1
    rw [Finset.card_range] at h2
    lia
  · intro hy
    by_contra hyS
    have h1 : S ⊆ Finset.range y := by
      intro b hb
      rw [Finset.mem_range]
      by_contra hb2
      exact hyS (h y b (by lia) hb)
    have h2 := Finset.card_le_card h1
    rw [Finset.card_range] at h2
    lia

/-- The blue points in column `x`. -/
def blueCol (n : ℕ) (color : ℕ × ℕ → Color) (x : ℕ) : Finset ℕ :=
  (Finset.range (n - x)).filter fun y ↦ color (x, y) = .blue

/-- The number of red points in column `x`. -/
def redCol (n : ℕ) (color : ℕ × ℕ → Color) (x : ℕ) : ℕ :=
  ((Finset.range (n - x)).filter fun y ↦ color (x, y) = .red).card

lemma card_blueCol (n : ℕ) (color : ℕ × ℕ → Color) (x : ℕ) :
    (blueCol n color x).card = n - x - redCol n color x := by
  have h1 : blueCol n color x =
      Finset.range (n - x) \ ((Finset.range (n - x)).filter fun y ↦ color (x, y) = .red) := by
    rw [blueCol, ← Finset.filter_not]
    exact Finset.filter_congr fun y _ ↦ color_eq_blue_iff _
  rw [h1, Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.filter_subset _ _),
    Finset.card_range, redCol]

lemma redCol_le (n : ℕ) (color : ℕ × ℕ → Color) (x : ℕ) : redCol n color x ≤ n - x :=
  le_trans (Finset.card_filter_le _ _) (Finset.card_range _).le

variable {n : ℕ} {color : ℕ × ℕ → Color}
  (hcolor : ∀ x' y' x y, x' ≤ x → y' ≤ y → x + y < n →
    color (x, y) = .red → color (x', y') = .red)

include hcolor

lemma red_iff {x y : ℕ} (hxy : x + y < n) :
    color (x, y) = .red ↔ y < redCol n color x := by
  have hdc : ∀ a b, a ≤ b →
      b ∈ (Finset.range (n - x)).filter (fun y ↦ color (x, y) = .red) →
      a ∈ (Finset.range (n - x)).filter (fun y ↦ color (x, y) = .red) := by
    intro a b hab hb
    rw [Finset.mem_filter, Finset.mem_range] at hb ⊢
    exact ⟨by lia, hcolor x a x b le_rfl hab (by lia) hb.2⟩
  have hyn : y < n - x := by lia
  rw [redCol, ← downward_closed_iff_lt_card hdc, Finset.mem_filter, Finset.mem_range]
  exact ⟨fun h ↦ ⟨hyn, h⟩, fun h ↦ h.2⟩

lemma redCol_antitone : Antitone (redCol n color) := by
  apply antitone_nat_of_succ_le
  intro x
  apply Finset.card_le_card
  intro y hy
  rw [Finset.mem_filter, Finset.mem_range] at hy ⊢
  exact ⟨by lia, hcolor x y (x + 1) y (by lia) le_rfl (by lia) hy.2⟩

/-- The red count in row `y` is the number of columns whose red count exceeds `y`. -/
lemma redCol_swap (y : ℕ) :
    redCol n (fun p ↦ color p.swap) y =
      ((Finset.range n).filter fun x ↦ y < redCol n color x).card := by
  rw [redCol]
  congr 1
  ext x
  rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_range, Finset.mem_range]
  constructor
  · rintro ⟨hx, hred⟩
    have hxy : x + y < n := by lia
    exact ⟨by lia, (red_iff hcolor hxy).mp hred⟩
  · rintro ⟨hx, hlt⟩
    have h1 : redCol n color x ≤ n - x := redCol_le n color x
    have hxy : x + y < n := by lia
    exact ⟨by lia, (red_iff hcolor hxy).mpr hlt⟩

omit hcolor

/-- The heart of the solution: if `f` is an antitone "red column count" function
fitting under the staircase, then the product of blue column counts equals the
product of blue row counts, where row red counts are given by the conjugate
partition. Induction on `∑ f`, recoloring one corner red point at a time. -/
lemma key_prod (n : ℕ) : ∀ N : ℕ, ∀ f : ℕ → ℕ, (∑ x ∈ Finset.range n, f x = N) →
    Antitone f → (∀ x, f x ≤ n - x) →
    ∏ x ∈ Finset.range n, (n - x - f x) =
      ∏ y ∈ Finset.range n, (n - y - ((Finset.range n).filter fun x ↦ y < f x).card) := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro f hsum hf hfle
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have h0 : ∀ x ∈ Finset.range n, f x = 0 := by
      intro x hx
      have h1 := Finset.single_le_sum (f := f) (fun i _ ↦ Nat.zero_le _) hx
      lia
    have hL : ∀ x ∈ Finset.range n, n - x - f x = n - x := fun x hx ↦ by rw [h0 x hx]; lia
    have hR : ∀ y ∈ Finset.range n,
        n - y - ((Finset.range n).filter fun x ↦ y < f x).card = n - y := by
      intro y hy
      have h2 : ((Finset.range n).filter fun x ↦ y < f x) = ∅ :=
        Finset.filter_false_of_mem fun x hx ↦ by rw [h0 x hx]; lia
      rw [h2, Finset.card_empty]
      lia
    rw [Finset.prod_congr rfl hL, Finset.prod_congr rfl hR]
  · -- pick the rightmost column containing a red point
    have hne : ((Finset.range n).filter fun x ↦ 0 < f x).Nonempty := by
      rw [Finset.filter_nonempty_iff]
      by_contra hc
      have h1 : ∑ x ∈ Finset.range n, f x = 0 :=
        Finset.sum_eq_zero fun x hx ↦ by
          rcases Nat.eq_zero_or_pos (f x) with h | h
          · exact h
          · exact absurd ⟨x, hx, h⟩ hc
      lia
    obtain ⟨x₀, hx₀mem, hx₀max⟩ : ∃ x₀ ∈ (Finset.range n).filter fun x ↦ 0 < f x,
        ∀ x ∈ (Finset.range n).filter fun x ↦ 0 < f x, x ≤ x₀ :=
      ⟨_, Finset.max'_mem _ hne, fun x hx ↦ Finset.le_max' _ x hx⟩
    rw [Finset.mem_filter, Finset.mem_range] at hx₀mem
    obtain ⟨hx₀n, hx₀pos⟩ := hx₀mem
    have hmax : ∀ x, x₀ < x → f x = 0 := by
      intro x hx
      rcases Nat.lt_or_ge x n with h | h
      · by_contra hfx
        have hmem : x ∈ (Finset.range n).filter fun x ↦ 0 < f x := by
          rw [Finset.mem_filter, Finset.mem_range]
          exact ⟨h, Nat.pos_of_ne_zero hfx⟩
        have := hx₀max x hmem
        lia
      · have := hfle x
        lia
    -- the corner red point is (x₀, y₀)
    obtain ⟨y₀, hy₀⟩ : ∃ y₀, f x₀ = y₀ + 1 := ⟨f x₀ - 1, by lia⟩
    have hx₀y₀ : x₀ + y₀ + 1 ≤ n := by
      have := hfle x₀
      lia
    -- recolor it blue
    set f' : ℕ → ℕ := Function.update f x₀ y₀ with hf'def
    have hf'x₀ : f' x₀ = y₀ := Function.update_self x₀ y₀ f
    have hf'ne : ∀ x, x ≠ x₀ → f' x = f x := fun x hx ↦ Function.update_of_ne hx y₀ f
    have hf' : Antitone f' := by
      intro a b hab
      rcases eq_or_ne b x₀ with rfl | hb
      · rcases eq_or_ne a b with rfl | ha
        · exact le_rfl
        · have h1 := hf hab
          rw [hf'x₀, hf'ne a ha]
          lia
      · rw [hf'ne b hb]
        rcases eq_or_ne a x₀ with rfl | ha
        · have hb2 : a < b := lt_of_le_of_ne hab (Ne.symm hb)
          rw [hf'x₀, hmax b hb2]
          exact Nat.zero_le _
        · rw [hf'ne a ha]
          exact hf hab
    have hfle' : ∀ x, f' x ≤ n - x := by
      intro x
      rcases eq_or_ne x x₀ with rfl | hx
      · have := hfle x
        rw [hf'x₀]
        lia
      · rw [hf'ne x hx]
        exact hfle x
    have hx₀rn : x₀ ∈ Finset.range n := Finset.mem_range.mpr hx₀n
    have hy₀rn : y₀ ∈ Finset.range n := Finset.mem_range.mpr (by lia)
    have hsum' : ∑ x ∈ Finset.range n, f' x = N - 1 := by
      have h1 : ∑ x ∈ Finset.range n, f' x =
          y₀ + ∑ x ∈ (Finset.range n).erase x₀, f x := by
        rw [hf'def, Finset.erase_eq]
        exact Finset.sum_update_of_mem hx₀rn f y₀
      have h2 : f x₀ + ∑ x ∈ (Finset.range n).erase x₀, f x =
          ∑ x ∈ Finset.range n, f x := Finset.add_sum_erase _ f hx₀rn
      lia
    have ihEq := ih (N - 1) (by lia) f' hsum' hf' hfle'
    -- row counts change only in row y₀, where they drop from x₀ + 1 to x₀
    have hcnt_ne : ∀ y, y ≠ y₀ →
        ((Finset.range n).filter fun x ↦ y < f' x) =
          ((Finset.range n).filter fun x ↦ y < f x) := by
      intro y hy
      apply Finset.filter_congr
      intro x _
      rcases eq_or_ne x x₀ with rfl | hxne
      · rw [hf'x₀, hy₀]
        constructor <;> intro <;> lia
      · rw [hf'ne x hxne]
    have hcnt_y₀ : ((Finset.range n).filter fun x ↦ y₀ < f x) = Finset.range (x₀ + 1) := by
      ext x
      rw [Finset.mem_filter, Finset.mem_range, Finset.mem_range]
      constructor
      · rintro ⟨hxn, hlt⟩
        by_contra hc
        rw [hmax x (by lia)] at hlt
        lia
      · intro hx
        have h1 : f x₀ ≤ f x := hf (by lia)
        exact ⟨by lia, by lia⟩
    have hcnt'_y₀ : ((Finset.range n).filter fun x ↦ y₀ < f' x) = Finset.range x₀ := by
      ext x
      rw [Finset.mem_filter, Finset.mem_range, Finset.mem_range]
      constructor
      · rintro ⟨hxn, hlt⟩
        rcases lt_trichotomy x x₀ with h | rfl | h
        · exact h
        · rw [hf'x₀] at hlt
          lia
        · rw [hf'ne x (by lia), hmax x h] at hlt
          lia
      · intro hx
        have h1 : f x₀ ≤ f x := hf (by lia)
        rw [hf'ne x (by lia)]
        exact ⟨by lia, by lia⟩
    -- split off the changed factor on each side
    have hL : ∏ x ∈ Finset.range n, (n - x - f x) =
        (n - x₀ - (y₀ + 1)) * ∏ x ∈ (Finset.range n).erase x₀, (n - x - f x) := by
      rw [← Finset.mul_prod_erase _ _ hx₀rn, hy₀]
    have hL' : ∏ x ∈ Finset.range n, (n - x - f' x) =
        (n - x₀ - y₀) * ∏ x ∈ (Finset.range n).erase x₀, (n - x - f x) := by
      rw [← Finset.mul_prod_erase _ _ hx₀rn, hf'x₀]
      congr 1
      exact Finset.prod_congr rfl fun x hx ↦ by rw [hf'ne x (Finset.ne_of_mem_erase hx)]
    have hR : ∏ y ∈ Finset.range n,
          (n - y - ((Finset.range n).filter fun x ↦ y < f x).card) =
        (n - y₀ - (x₀ + 1)) * ∏ y ∈ (Finset.range n).erase y₀,
          (n - y - ((Finset.range n).filter fun x ↦ y < f x).card) := by
      rw [← Finset.mul_prod_erase _ _ hy₀rn, hcnt_y₀, Finset.card_range]
    have hR' : ∏ y ∈ Finset.range n,
          (n - y - ((Finset.range n).filter fun x ↦ y < f' x).card) =
        (n - y₀ - x₀) * ∏ y ∈ (Finset.range n).erase y₀,
          (n - y - ((Finset.range n).filter fun x ↦ y < f x).card) := by
      rw [← Finset.mul_prod_erase _ _ hy₀rn, hcnt'_y₀, Finset.card_range]
      congr 1
      exact Finset.prod_congr rfl fun y hy ↦ by rw [hcnt_ne y (Finset.ne_of_mem_erase hy)]
    rw [hL', hR'] at ihEq
    have hk : n - x₀ - y₀ = n - y₀ - x₀ := by lia
    rw [hk] at ihEq
    have hcancel := Nat.eq_of_mul_eq_mul_left (by lia : 0 < n - y₀ - x₀) ihEq
    rw [hL, hR, hcancel]
    congr 1
    lia

lemma image_fst_eq {s : Finset (ℕ × ℕ)}
    (hs : s ∈ ((T n).powersetCard n).filter fun s ↦
      (∀ p ∈ s, color p = .blue) ∧ ∀ p ∈ s, ∀ q ∈ s, p.1 = q.1 → p = q) :
    s.image Prod.fst = Finset.range n := by
  rw [Finset.mem_filter, Finset.mem_powersetCard] at hs
  obtain ⟨⟨hsub, hcard⟩, _hblue, hinj⟩ := hs
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨p, hp, rfl⟩ := hx
    have hpT := hsub hp
    simp only [T, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hpT
    exact Finset.mem_range.mpr (by lia)
  · rw [Finset.card_range, Finset.card_image_of_injOn fun p hp q hq h ↦ hinj p hp q hq h]
    lia

lemma exists_unique_fst {s : Finset (ℕ × ℕ)}
    (hs : s ∈ ((T n).powersetCard n).filter fun s ↦
      (∀ p ∈ s, color p = .blue) ∧ ∀ p ∈ s, ∀ q ∈ s, p.1 = q.1 → p = q)
    {x : ℕ} (hx : x ∈ Finset.range n) :
    ∃! p, p ∈ s ∧ p.1 = x := by
  have himg := image_fst_eq hs
  rw [Finset.mem_filter] at hs
  obtain ⟨_, _, hinj⟩ := hs
  have hx2 : x ∈ s.image Prod.fst := by rw [himg]; exact hx
  rw [Finset.mem_image] at hx2
  obtain ⟨p, hp, hpx⟩ := hx2
  exact ⟨p, ⟨hp, hpx⟩, fun q ⟨hq, hqx⟩ ↦ hinj q hq p hp (by rw [hqx, hpx])⟩

/-- A choice of n blue points with distinct x-coordinates amounts to a choice
of one blue point in each column. -/
lemma choiceCount_fst (n : ℕ) (color : ℕ × ℕ → Color) :
    ChoiceCount n color Prod.fst = ∏ x ∈ Finset.range n, (blueCol n color x).card := by
  rw [ChoiceCount, ← Finset.card_pi]
  refine Finset.card_bij'
    (fun s hs ↦ fun x hx ↦ (Finset.choose (fun q ↦ q.1 = x) s (exists_unique_fst hs hx)).2)
    (fun p _ ↦ (Finset.range n).attach.image
      fun x : {a // a ∈ Finset.range n} ↦ (x.1, p x.1 x.2))
    ?_ ?_ ?_ ?_
  · intro s hs
    rw [Finset.mem_pi]
    intro x hx
    have hPmem := Finset.choose_mem (fun q ↦ q.1 = x) s (exists_unique_fst hs hx)
    have hP1 : (Finset.choose (fun q ↦ q.1 = x) s (exists_unique_fst hs hx)).1 = x :=
      Finset.choose_property (fun q ↦ q.1 = x) s (exists_unique_fst hs hx)
    rw [Finset.mem_filter, Finset.mem_powersetCard] at hs
    obtain ⟨⟨hsub, _⟩, hblue, _⟩ := hs
    have hPT := hsub hPmem
    simp only [T, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hPT
    rw [blueCol, Finset.mem_filter, Finset.mem_range]
    constructor
    · lia
    · have heta : (x, (Finset.choose (fun q ↦ q.1 = x) s (exists_unique_fst hs hx)).2) =
          Finset.choose (fun q ↦ q.1 = x) s (exists_unique_fst hs hx) :=
        Prod.ext hP1.symm rfl
      rw [heta]
      exact hblue _ hPmem
  · intro p hp
    rw [Finset.mem_pi] at hp
    rw [Finset.mem_filter, Finset.mem_powersetCard]
    have hmem : ∀ x (hx : x ∈ Finset.range n), p x hx < n - x ∧ color (x, p x hx) = .blue := by
      intro x hx
      have := hp x hx
      rw [blueCol, Finset.mem_filter, Finset.mem_range] at this
      exact this
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · intro q hq
      rw [Finset.mem_image] at hq
      obtain ⟨⟨x, hx⟩, -, rfl⟩ := hq
      have h1 := (hmem x hx).1
      have h2 := Finset.mem_range.mp hx
      simp only [T, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      refine ⟨⟨by lia, by lia⟩, by lia⟩
    · rw [Finset.card_image_of_injOn, Finset.card_attach, Finset.card_range]
      intro a _ b _ hab
      have : (a : ℕ) = (b : ℕ) := congrArg Prod.fst hab
      exact Subtype.ext this
    · intro q hq
      rw [Finset.mem_image] at hq
      obtain ⟨⟨x, hx⟩, -, rfl⟩ := hq
      exact (hmem x hx).2
    · intro q hq r hr hqr
      rw [Finset.mem_image] at hq hr
      obtain ⟨⟨x, hx⟩, -, rfl⟩ := hq
      obtain ⟨⟨x', hx'⟩, -, rfl⟩ := hr
      have : x = x' := hqr
      subst this
      rfl
  · intro s hs
    ext q
    rw [Finset.mem_image]
    constructor
    · rintro ⟨⟨x, hx⟩, -, rfl⟩
      have hPmem := Finset.choose_mem (fun q ↦ q.1 = x) s (exists_unique_fst hs hx)
      have hP1 : (Finset.choose (fun q ↦ q.1 = x) s (exists_unique_fst hs hx)).1 = x :=
        Finset.choose_property (fun q ↦ q.1 = x) s (exists_unique_fst hs hx)
      have heta : (x, (Finset.choose (fun q ↦ q.1 = x) s (exists_unique_fst hs hx)).2) =
          Finset.choose (fun q ↦ q.1 = x) s (exists_unique_fst hs hx) :=
        Prod.ext hP1.symm rfl
      rw [heta]
      exact hPmem
    · intro hq
      have hq1 : q.1 ∈ Finset.range n := by
        rw [← image_fst_eq hs]
        exact Finset.mem_image_of_mem Prod.fst hq
      refine ⟨⟨q.1, hq1⟩, Finset.mem_attach _ _, ?_⟩
      show (q.1, (Finset.choose (fun r ↦ r.1 = q.1) s (exists_unique_fst hs hq1)).2) = q
      have h1 := (exists_unique_fst hs hq1).unique
        ⟨Finset.choose_mem (fun r ↦ r.1 = q.1) s (exists_unique_fst hs hq1),
         Finset.choose_property (fun r ↦ r.1 = q.1) s (exists_unique_fst hs hq1)⟩
        ⟨hq, rfl⟩
      rw [h1]
  · intro p hp
    funext x hx
    have hgen : ∀ q ∈ (Finset.range n).attach.image
        (fun x : {a // a ∈ Finset.range n} ↦ (x.1, p x.1 x.2)),
        q.1 = x → q.2 = p x hx := by
      rintro q hq hq1
      rw [Finset.mem_image] at hq
      obtain ⟨⟨x', hx'⟩, -, rfl⟩ := hq
      have hxx : x' = x := hq1
      subst hxx
      rfl
    apply hgen
    · exact Finset.choose_mem (fun q : ℕ × ℕ ↦ q.1 = x) _ _
    · exact Finset.choose_property (fun q : ℕ × ℕ ↦ q.1 = x) _ _

/-- Reflecting across the diagonal swaps the roles of the two coordinates. -/
lemma choiceCount_snd (n : ℕ) (color : ℕ × ℕ → Color) :
    ChoiceCount n color Prod.snd = ChoiceCount n (fun p ↦ color p.swap) Prod.fst := by
  rw [ChoiceCount, ChoiceCount]
  refine Finset.card_bij' (fun s _ ↦ s.image Prod.swap) (fun s _ ↦ s.image Prod.swap)
    ?_ ?_ ?_ ?_
  · intro s hs
    rw [Finset.mem_filter, Finset.mem_powersetCard] at hs ⊢
    obtain ⟨⟨hsub, hcard⟩, hblue, hinj⟩ := hs
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · intro q hq
      rw [Finset.mem_image] at hq
      obtain ⟨r, hr, rfl⟩ := hq
      have := hsub hr
      simp only [T, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
        Prod.fst_swap, Prod.snd_swap] at this ⊢
      lia
    · rw [Finset.card_image_of_injective _ Prod.swap_injective, hcard]
    · intro q hq
      rw [Finset.mem_image] at hq
      obtain ⟨r, hr, rfl⟩ := hq
      rw [Prod.swap_swap]
      exact hblue r hr
    · intro q hq r hr hqr
      rw [Finset.mem_image] at hq hr
      obtain ⟨q', hq', rfl⟩ := hq
      obtain ⟨r', hr', rfl⟩ := hr
      rw [Prod.fst_swap, Prod.fst_swap] at hqr
      rw [hinj q' hq' r' hr' hqr]
  · intro s hs
    rw [Finset.mem_filter, Finset.mem_powersetCard] at hs ⊢
    obtain ⟨⟨hsub, hcard⟩, hblue, hinj⟩ := hs
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · intro q hq
      rw [Finset.mem_image] at hq
      obtain ⟨r, hr, rfl⟩ := hq
      have := hsub hr
      simp only [T, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
        Prod.fst_swap, Prod.snd_swap] at this ⊢
      lia
    · rw [Finset.card_image_of_injective _ Prod.swap_injective, hcard]
    · intro q hq
      rw [Finset.mem_image] at hq
      obtain ⟨r, hr, rfl⟩ := hq
      exact hblue r hr
    · intro q hq r hr hqr
      rw [Finset.mem_image] at hq hr
      obtain ⟨q', hq', rfl⟩ := hq
      obtain ⟨r', hr', rfl⟩ := hr
      rw [Prod.snd_swap, Prod.snd_swap] at hqr
      rw [hinj q' hq' r' hr' hqr]
  · intro s _
    rw [Finset.image_image]
    simp
  · intro s _
    rw [Finset.image_image]
    simp

snip end

problem imo2002_p1 (n : ℕ) (_hn : 0 < n) (color : ℕ × ℕ → Color)
    (hcolor : ∀ x' y' x y, x' ≤ x → y' ≤ y → x + y < n →
      color (x, y) = .red → color (x', y') = .red) :
    ChoiceCount n color Prod.fst = ChoiceCount n color Prod.snd := by
  have hcolor' : ∀ x' y' x y, x' ≤ x → y' ≤ y → x + y < n →
      (fun p ↦ color p.swap) (x, y) = .red → (fun p ↦ color p.swap) (x', y') = .red := by
    intro x' y' x y hx hy hxy hred
    exact hcolor y' x' y x hy hx (by lia) hred
  rw [choiceCount_fst, choiceCount_snd n color, choiceCount_fst]
  have h1 : ∀ x ∈ Finset.range n, (blueCol n color x).card = n - x - redCol n color x :=
    fun x _ ↦ card_blueCol n color x
  have h2 : ∀ y ∈ Finset.range n, (blueCol n (fun p ↦ color p.swap) y).card =
      n - y - ((Finset.range n).filter fun x ↦ y < redCol n color x).card := by
    intro y _
    rw [card_blueCol, redCol_swap hcolor y]
  rw [Finset.prod_congr rfl h1, Finset.prod_congr rfl h2]
  exact key_prod n (∑ x ∈ Finset.range n, redCol n color x) (redCol n color) rfl
    (redCol_antitone hcolor) (redCol_le n color)


end Imo2002P1
