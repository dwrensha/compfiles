/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Int.Star
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics, .Geometry] }

/-!
# USA Mathematical Olympiad 2005, Problem 5

Let n > 1 be an integer. Suppose 2n points are given in the plane, no three of which
are collinear. Suppose n of the given 2n points are colored blue and the other n
colored red. A line in the plane is called a balancing line if it passes through one
blue and one red point and, for each side of the line, the number of blue points on
that side is equal to the number of red points on the same side. Prove that there
exist at least two balancing lines.
-/

namespace Usa2005P5

open Classical

/-- The cross product (signed area) of two vectors in the plane. Points `a`, `b`, `c`
are collinear iff `cross (b - a) (c - a) = 0`, and otherwise the sign tells on which
side of the directed line through `a` and `b` the point `c` lies. -/
def cross (u v : ℝ × ℝ) : ℝ := u.1 * v.2 - u.2 * v.1

/-- The line through the blue point `b` and the red point `r` is *balancing* if on
each of its two open sides the number of blue points equals the number of red points.
We express "the two sides of the line" with the sign of the cross product. -/
noncomputable def Balancing {n : ℕ} (point : Fin (2 * n) → ℝ × ℝ)
    (color : Fin (2 * n) → Bool) (b r : Fin (2 * n)) : Prop :=
  (Finset.univ.filter fun k ↦
      0 < cross (point r - point b) (point k - point b) ∧ color k = true).card =
    (Finset.univ.filter fun k ↦
      0 < cross (point r - point b) (point k - point b) ∧ color k = false).card ∧
  (Finset.univ.filter fun k ↦
      cross (point r - point b) (point k - point b) < 0 ∧ color k = true).card =
    (Finset.univ.filter fun k ↦
      cross (point r - point b) (point k - point b) < 0 ∧ color k = false).card

snip begin

lemma cross_anti (u v : ℝ × ℝ) : cross u v = -cross v u := by
  simp only [cross]; ring

lemma cross_self (u : ℝ × ℝ) : cross u u = 0 := by
  simp only [cross]; ring

lemma cross_zero_left (v : ℝ × ℝ) : cross 0 v = 0 := by
  show (0 : ℝ) * v.2 - (0 : ℝ) * v.1 = 0; ring

lemma cross_zero_right (u : ℝ × ℝ) : cross u 0 = 0 := by
  show u.1 * (0 : ℝ) - u.2 * (0 : ℝ) = 0; ring

lemma cross_add_right (u v w : ℝ × ℝ) : cross u (v + w) = cross u v + cross u w := by
  simp only [cross, Prod.fst_add, Prod.snd_add]; ring

lemma cross_sub_right (u v w : ℝ × ℝ) : cross u (v - w) = cross u v - cross u w := by
  simp only [cross, Prod.fst_sub, Prod.snd_sub]; ring

lemma cross_add_left (u v w : ℝ × ℝ) : cross (u + v) w = cross u w + cross v w := by
  simp only [cross, Prod.fst_add, Prod.snd_add]; ring

lemma cross_sub_left (u v w : ℝ × ℝ) : cross (u - v) w = cross u w - cross v w := by
  simp only [cross, Prod.fst_sub, Prod.snd_sub]; ring

lemma cross_neg_left (u v : ℝ × ℝ) : cross (-u) v = -cross u v := by
  simp only [cross, Prod.fst_neg, Prod.snd_neg]; ring

lemma cross_neg_right (u v : ℝ × ℝ) : cross u (-v) = -cross u v := by
  simp only [cross, Prod.fst_neg, Prod.snd_neg]; ring

lemma cross_smul_left (u v : ℝ × ℝ) (a : ℝ) : cross (a • u) v = a * cross u v := by
  show (a * u.1) * v.2 - (a * u.2) * v.1 = a * (u.1 * v.2 - u.2 * v.1); ring

lemma cross_smul_right (u v : ℝ × ℝ) (a : ℝ) : cross u (a • v) = a * cross u v := by
  show u.1 * (a * v.2) - u.2 * (a * v.1) = a * (u.1 * v.2 - u.2 * v.1); ring

/-- The Plücker relation between cross products of four vectors in the plane. -/
lemma plucker (d u v w : ℝ × ℝ) :
    cross u v * cross d w + cross v w * cross d u = cross u w * cross d v := by
  simp only [cross]; ring

/-- The "counterclockwise" relation between vectors lying in a common open half-plane
is transitive. This is the algebraic content of angle addition in a half-plane. -/
lemma cross_trans {d u v w : ℝ × ℝ} (hdu : 0 < cross d u) (hdv : 0 < cross d v)
    (hdw : 0 < cross d w) (huv : 0 < cross u v) (hvw : 0 < cross v w) :
    0 < cross u w :=
  (mul_pos_iff_of_pos_right hdv).mp <| by
    have h1 : 0 < cross u v * cross d w := mul_pos huv hdw
    have h2 : 0 < cross v w * cross d u := mul_pos hvw hdu
    linarith [plucker d u v w]

/-- The standard dot product in the plane (used in the proof). -/
def dot (u v : ℝ × ℝ) : ℝ := u.1 * v.1 + u.2 * v.2

lemma dot_sub (u v w : ℝ × ℝ) : dot u (v - w) = dot u v - dot u w := by
  simp only [dot, Prod.fst_sub, Prod.snd_sub]; ring

/-- A nonzero vector `u` detects linear independence: only the zero vector is both
`cross`-orthogonal and `dot`-orthogonal to `u`. -/
lemma cross_dot_eq_zero {u v : ℝ × ℝ} (hu : u ≠ 0) (hc : cross u v = 0)
    (hd : dot u v = 0) : v = 0 := by
  have hc' : u.1 * v.2 - u.2 * v.1 = 0 := hc
  have hd' : u.1 * v.1 + u.2 * v.2 = 0 := hd
  have hu12 : 0 < u.1 ^ 2 + u.2 ^ 2 := by
    have h : u.1 ≠ 0 ∨ u.2 ≠ 0 := by
      by_contra! h'
      exact hu (Prod.ext h'.1 h'.2)
    rcases h with h | h
    · have h1 : 0 < u.1 ^ 2 := sq_pos_of_ne_zero h
      have h2 := sq_nonneg u.2
      linarith
    · have h1 : 0 < u.2 ^ 2 := sq_pos_of_ne_zero h
      have h2 := sq_nonneg u.1
      linarith
  have e1 : (u.1 ^ 2 + u.2 ^ 2) * v.1 = 0 := by linear_combination u.1 * hd' - u.2 * hc'
  have e2 : (u.1 ^ 2 + u.2 ^ 2) * v.2 = 0 := by linear_combination u.2 * hd' + u.1 * hc'
  have hne : (u.1 ^ 2 + u.2 ^ 2) ≠ 0 := ne_of_gt hu12
  exact Prod.ext (by simpa [hne] using e1) (by simpa [hne] using e2)

/-- A point of a finite configuration is *extreme* if some line through it has all
other points strictly on one side (equivalently, it is a vertex of the convex hull). -/
def Extreme {m : ℕ} (point : Fin m → ℝ × ℝ) (i : Fin m) : Prop :=
  ∃ d : ℝ × ℝ, ∀ j : Fin m, j ≠ i → 0 < cross d (point j - point i)

/-- In a configuration of `2n ≥ 4` points, some point avoids any given pair. -/
lemma exists_ne_two {n : ℕ} (hn : 1 < n) (i j : Fin (2 * n)) :
    ∃ k : Fin (2 * n), k ≠ i ∧ k ≠ j := by
  classical
  have hcard : 2 < (Finset.univ : Finset (Fin (2 * n))).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    omega
  have hne : (Finset.univ \ {i, j}).Nonempty := by
    rw [← Finset.card_pos, Finset.card_sdiff, Finset.inter_univ]
    have h2 : ({i, j} : Finset (Fin (2 * n))).card ≤ 2 := by
      rcases eq_or_ne i j with h | h
      · subst h; simp
      · simp [Finset.card_pair h]
    omega
  obtain ⟨k, hk⟩ := hne
  have hk' : k ∉ ({i, j} : Finset (Fin (2 * n))) := (Finset.mem_sdiff.mp hk).2
  exact ⟨k, by simpa using hk'⟩

/-- "No three points collinear" forces the points of a `2n ≥ 4` configuration to be
distinct. -/
lemma injective_of_hnc {n : ℕ} (hn : 1 < n) (point : Fin (2 * n) → ℝ × ℝ)
    (hnc : ∀ i j k : Fin (2 * n), i ≠ j → j ≠ k → i ≠ k →
      cross (point j - point i) (point k - point i) ≠ 0) :
    Function.Injective point := by
  intro i j hij
  by_contra hne
  obtain ⟨k, hk1, hk2⟩ := exists_ne_two hn i j
  apply hnc i j k hne hk2.symm hk1.symm
  have e : point j - point i = 0 := sub_eq_zero.mpr hij.symm
  rw [e]
  exact cross_zero_left _

/-- The lexicographically largest point (by first, then second coordinate) of an
injective finite configuration is extreme. -/
lemma exists_extreme_lexmax {m : ℕ} (point : Fin m → ℝ × ℝ)
    (hinj : Function.Injective point) (hm : 0 < m) :
    ∃ i : Fin m, Extreme point i ∧ (∀ j, (point j).1 ≤ (point i).1) ∧
      (∀ j, (point j).1 = (point i).1 → (point j).2 ≤ (point i).2) := by
  classical
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  obtain ⟨a, -, ha⟩ := Finset.exists_max_image Finset.univ (fun j ↦ (point j).1)
    Finset.univ_nonempty
  obtain ⟨i, hiS, hi⟩ := Finset.exists_max_image
    (Finset.univ.filter fun j ↦ (point j).1 = (point a).1) (fun j ↦ (point j).2)
    ⟨a, by simp⟩
  have hi1 : (point i).1 = (point a).1 := by
    have h := hiS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
    exact h
  have hle1 : ∀ j, (point j).1 ≤ (point i).1 := fun j ↦
    (ha j (Finset.mem_univ j)).trans (le_of_eq hi1.symm)
  have hle2 : ∀ j, (point j).1 = (point i).1 → (point j).2 ≤ (point i).2 := fun j hj ↦
    hi j (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hj.trans hi1)
  refine ⟨i, ?_, hle1, hle2⟩
  -- choose a sufficiently steep slope `K`
  set ratio : Fin m → ℝ := fun j ↦
    if 0 < (point j - point i).2 ∧ (point j - point i).1 < 0
    then (point j - point i).2 / (-(point j - point i).1) else 0 with hratio
  set K : ℝ := 1 + ∑ j : Fin m, ratio j with hK
  have hterm : ∀ j, 0 ≤ ratio j := by
    intro j
    show 0 ≤ (if 0 < (point j - point i).2 ∧ (point j - point i).1 < 0
      then (point j - point i).2 / (-(point j - point i).1) else 0)
    split_ifs with h
    · exact le_of_lt (div_pos h.1 (neg_pos.mpr h.2))
    · exact le_refl 0
  have hK1 : 1 ≤ K := by
    have h := Finset.sum_nonneg (s := Finset.univ) (f := ratio) (fun j _ ↦ hterm j)
    linarith
  refine ⟨(-1, K), fun j hji ↦ ?_⟩
  have hu1 : (point j - point i).1 ≤ 0 := sub_nonpos.mpr (hle1 j)
  have hpos : (0:ℝ) < -1 * (point j - point i).2 - K * (point j - point i).1 := by
    by_cases h1 : (point j - point i).1 = 0
    · -- same first coordinate: the point is strictly below
      have h2lt : (point j - point i).2 < 0 := by
        have hle : (point j - point i).2 ≤ 0 := sub_nonpos.mpr (hle2 j (sub_eq_zero.mp h1))
        have hne : point j ≠ point i := fun h ↦ hji (hinj h)
        exact lt_of_le_of_ne hle
          (fun heq ↦ hne (Prod.ext (sub_eq_zero.mp h1) (sub_eq_zero.mp heq)))
      have e : -1 * (point j - point i).2 - K * (point j - point i).1 =
          -(point j - point i).2 := by
        rw [h1]; ring
      rw [e]
      exact neg_pos.mpr h2lt
    · have h1lt : (point j - point i).1 < 0 := lt_of_le_of_ne hu1 h1
      by_cases h2 : 0 < (point j - point i).2
      · -- the steep slope beats this ratio
        have hrj : ratio j = (point j - point i).2 / (-(point j - point i).1) :=
          if_pos ⟨h2, h1lt⟩
        have hlt : (point j - point i).2 / (-(point j - point i).1) < K := by
          have hs := Finset.single_le_sum (fun i' _ ↦ hterm i') (Finset.mem_univ j)
          rw [hrj] at hs
          linarith [hK]
        have hmul : (point j - point i).2 < K * (-(point j - point i).1) :=
          (div_lt_iff₀ (neg_pos.mpr h1lt)).mp hlt
        have e : -1 * (point j - point i).2 - K * (point j - point i).1 =
            K * (-(point j - point i).1) - (point j - point i).2 := by ring
        rw [e]
        linarith [hmul]
      · push Not at h2
        have hpos1 : (0:ℝ) < -(point j - point i).1 := neg_pos.mpr h1lt
        have hKpos : 0 < K := lt_of_lt_of_le one_pos hK1
        have hmul : 0 < K * (-(point j - point i).1) := mul_pos hKpos hpos1
        have e : -1 * (point j - point i).2 - K * (point j - point i).1 =
            -(point j - point i).2 + K * (-(point j - point i).1) := by ring
        rw [e]
        linarith [h2, hmul]
  exact hpos

/-- The lexicographically smallest point of an injective finite configuration is
extreme. -/
lemma exists_extreme_lexmin {m : ℕ} (point : Fin m → ℝ × ℝ)
    (hinj : Function.Injective point) (hm : 0 < m) :
    ∃ i : Fin m, Extreme point i ∧ (∀ j, (point i).1 ≤ (point j).1) ∧
      (∀ j, (point j).1 = (point i).1 → (point i).2 ≤ (point j).2) := by
  have hinj' : Function.Injective (fun j ↦ (-(point j).1, -(point j).2)) := by
    intro a b h
    apply hinj
    have h1 : -(point a).1 = -(point b).1 := congrArg Prod.fst h
    have h2 : -(point a).2 = -(point b).2 := congrArg Prod.snd h
    exact Prod.ext (neg_inj.mp h1) (neg_inj.mp h2)
  obtain ⟨i, hE, h1, h2⟩ :=
    exists_extreme_lexmax (fun j ↦ (-(point j).1, -(point j).2)) hinj' hm
  refine ⟨i, ?_, fun j ↦ neg_le_neg_iff.mp (h1 j),
    fun j hj ↦ neg_le_neg_iff.mp (h2 j (congrArg Neg.neg hj))⟩
  obtain ⟨d, hd⟩ := hE
  refine ⟨-d, fun j hji ↦ ?_⟩
  have h := hd j hji
  have h' : (0:ℝ) < cross d ((-(point j).1, -(point j).2) - (-(point i).1, -(point i).2)) := h
  have heq : -(point j - point i) =
      (-(point j).1, -(point j).2) - (-(point i).1, -(point i).2) :=
    Prod.ext (by show -((point j).1 - (point i).1) = -(point j).1 - -(point i).1; ring)
      (by show -((point j).2 - (point i).2) = -(point j).2 - -(point i).2; ring)
  rw [← heq, cross_neg_right] at h'
  rw [cross_neg_left]
  exact h'

/-- If the maximal `cross`-value over the points measured from the directed line
through two distinct points `A`, `B` is positive, then a maximizing point (with ties
broken along the line) is extreme, and it differs from `A` and `B`. -/
lemma extreme_of_pos_max {m : ℕ} (point : Fin m → ℝ × ℝ)
    (hinj : Function.Injective point) {A B : Fin m} (hAB : A ≠ B)
    (c₀ : Fin m) (hc₀ : ∀ j, cross (point B - point A) (point j - point A) ≤
      cross (point B - point A) (point c₀ - point A))
    (hM : 0 < cross (point B - point A) (point c₀ - point A)) :
    ∃ C : Fin m, Extreme point C ∧ C ≠ A ∧ C ≠ B := by
  classical
  haveI : Nonempty (Fin m) := ⟨A⟩
  set u := point B - point A with hu
  set M := cross u (point c₀ - point A) with hMdef
  obtain ⟨C, hCS, hC⟩ := Finset.exists_max_image
    (Finset.univ.filter fun j ↦ cross u (point j - point A) = M) (fun j ↦ dot u (point j))
    ⟨c₀, by simp [hMdef]⟩
  have hCM : cross u (point C - point A) = M := by
    have h := hCS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
    exact h
  have hu0 : u ≠ 0 := by
    intro h
    rw [hu] at h
    exact hAB (hinj (sub_eq_zero.mp h)).symm
  have hCA : C ≠ A := by
    intro h
    subst h
    rw [sub_self, cross_zero_right] at hCM
    rw [← hCM] at hM
    exact lt_irrefl 0 hM
  have hCB : C ≠ B := by
    intro h
    subst h
    rw [← hu, cross_self] at hCM
    rw [← hCM] at hM
    exact lt_irrefl 0 hM
  refine ⟨C, ?_, hCA, hCB⟩
  -- choose a sufficiently large tilt `K`
  set ratio : Fin m → ℝ := fun j ↦
    if cross u (point j - point C) < 0 ∧ 0 < dot u (point j - point C)
    then dot u (point j - point C) / (-(cross u (point j - point C))) else 0 with hratio
  set K : ℝ := 1 + ∑ j : Fin m, ratio j with hK
  have hterm : ∀ j, 0 ≤ ratio j := by
    intro j
    show 0 ≤ (if cross u (point j - point C) < 0 ∧ 0 < dot u (point j - point C)
      then dot u (point j - point C) / (-(cross u (point j - point C))) else 0)
    split_ifs with h
    · exact le_of_lt (div_pos h.2 (neg_pos.mpr h.1))
    · exact le_refl 0
  have hK1 : 1 ≤ K := by
    have h := Finset.sum_nonneg (s := Finset.univ) (f := ratio) (fun j _ ↦ hterm j)
    linarith
  refine ⟨(-u.2, u.1) - K • u, fun j hjC ↦ ?_⟩
  set v := point j - point C with hv
  have hv' : v = (point j - point A) - (point C - point A) :=
    Prod.ext (by show (point j).1 - (point C).1 =
        (point j).1 - (point A).1 - ((point C).1 - (point A).1); ring)
      (by show (point j).2 - (point C).2 =
        (point j).2 - (point A).2 - ((point C).2 - (point A).2); ring)
  have huv : cross u v = cross u (point j - point A) - M := by
    rw [hv', cross_sub_right, hCM]
  have huvle : cross u v ≤ 0 := by linarith [hc₀ j]
  have hperp : ∀ w : ℝ × ℝ, cross ((-u.2, u.1) : ℝ × ℝ) w = -dot u w := fun w ↦ by
    show (-u.2) * w.2 - u.1 * w.1 = -(u.1 * w.1 + u.2 * w.2); ring
  have hcross : cross (((-u.2, u.1) : ℝ × ℝ) - K • u) v = -dot u v - K * cross u v := by
    rw [cross_sub_left, cross_smul_left, hperp]
  rw [hcross]
  rcases lt_or_eq_of_le huvle with hlt | heq
  · -- the point is strictly below the line through `C`
    by_cases hdot : 0 < dot u v
    · have hrj : ratio j = dot u v / (-(cross u v)) := if_pos ⟨hlt, hdot⟩
      have hlt2 : dot u v / (-(cross u v)) < K := by
        have hs := Finset.single_le_sum (fun i' _ ↦ hterm i') (Finset.mem_univ j)
        rw [hrj] at hs
        linarith [hK]
      have hmul : dot u v < K * (-(cross u v)) :=
        (div_lt_iff₀ (neg_pos.mpr hlt)).mp hlt2
      have e : -dot u v - K * cross u v = K * (-(cross u v)) - dot u v := by ring
      rw [e]
      linarith [hmul]
    · push Not at hdot
      have hKpos : 0 < K := lt_of_lt_of_le one_pos hK1
      have hmul : 0 < K * (-(cross u v)) := mul_pos hKpos (neg_pos.mpr hlt)
      have e : -dot u v - K * cross u v = -(dot u v) + K * (-(cross u v)) := by ring
      rw [e]
      linarith [hdot, hmul]
  · -- the point is on the parallel through `C`, hence strictly behind `C`
    have hjeq : cross u (point j - point A) = M := by linarith [huv, heq]
    have hdotle : dot u v ≤ 0 := by
      have h := hC j (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hjeq)
      have hdotv : dot u v = dot u (point j) - dot u (point C) := by
        rw [hv', dot_sub, dot_sub, dot_sub]; ring
      linarith [h, hdotv.le]
    have hdotlt : dot u v < 0 := by
      rcases eq_or_lt_of_le hdotle with h | h
      · exfalso
        have hv0 : v = 0 := cross_dot_eq_zero hu0 heq h
        rw [hv] at hv0
        exact hjC (hinj (sub_eq_zero.mp hv0))
      · exact h
    rw [heq]
    linarith [neg_pos.mpr hdotlt]

/-- Given two distinct points `A`, `B` of an injective configuration with a point off
the line `AB`, there is a third extreme point `C` distinct from both. -/
lemma exists_third_extreme {m : ℕ} (point : Fin m → ℝ × ℝ)
    (hinj : Function.Injective point) {A B : Fin m} (hAB : A ≠ B)
    (h : ∃ j, cross (point B - point A) (point j - point A) ≠ 0) :
    ∃ C : Fin m, Extreme point C ∧ C ≠ A ∧ C ≠ B := by
  classical
  haveI : Nonempty (Fin m) := ⟨A⟩
  obtain ⟨c₀, -, hc₀⟩ := Finset.exists_max_image Finset.univ
    (fun j ↦ cross (point B - point A) (point j - point A)) Finset.univ_nonempty
  set M := cross (point B - point A) (point c₀ - point A) with hMdef
  have swapRoute : M ≤ 0 → ∃ C : Fin m, Extreme point C ∧ C ≠ A ∧ C ≠ B := by
    intro hM
    -- all points are on one side of `AB`; swap the roles of `A` and `B`
    obtain ⟨j₀, hj₀⟩ := h
    have hj₀lt : cross (point B - point A) (point j₀ - point A) < 0 :=
      lt_of_le_of_ne (le_trans (hc₀ j₀ (Finset.mem_univ j₀)) hM) hj₀
    obtain ⟨c₁, -, hc₁⟩ := Finset.exists_min_image Finset.univ
      (fun j ↦ cross (point B - point A) (point j - point A)) Finset.univ_nonempty
    have key : ∀ j, cross (point A - point B) (point j - point B) =
        -cross (point B - point A) (point j - point A) := fun j ↦ by
      simp only [cross, Prod.fst_sub, Prod.snd_sub]; ring
    have hc₁max : ∀ j, cross (point A - point B) (point j - point B) ≤
        cross (point A - point B) (point c₁ - point B) := by
      intro j
      rw [key, key]
      have h := hc₁ j (Finset.mem_univ j)
      linarith
    have hpos : 0 < cross (point A - point B) (point c₁ - point B) := by
      rw [key]
      have h := hc₁ j₀ (Finset.mem_univ j₀)
      linarith [h, hj₀lt]
    obtain ⟨C, hCE, hC1, hC2⟩ := extreme_of_pos_max point hinj hAB.symm c₁ hc₁max hpos
    exact ⟨C, hCE, hC2, hC1⟩
  rcases le_total M 0 with hM | hM
  · exact swapRoute hM
  · rcases eq_or_lt_of_le hM with hMeq | hMlt
    · exact swapRoute (le_of_eq hMeq.symm)
    · exact extreme_of_pos_max point hinj hAB c₀ (fun j ↦ hc₀ j (Finset.mem_univ j)) hMlt

/-- The blue count is `n`, derived from the red count. -/
lemma blue_card {n : ℕ} (color : Fin (2 * n) → Bool)
    (hred : (Finset.univ.filter fun i ↦ color i = true).card = n) :
    (Finset.univ.filter fun i ↦ color i = false).card = n := by
  classical
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin (2 * n))))
    (p := fun i ↦ color i = true)
  rw [Finset.card_univ, Fintype.card_fin, hred] at h
  have hconv : (Finset.univ.filter fun i ↦ ¬ color i = true) =
      (Finset.univ.filter fun i ↦ color i = false) :=
    Finset.filter_congr (fun x _ ↦ by rw [Bool.not_eq_true])
  rw [hconv] at h
  omega

/-- The sweep step: rotating a ray about an extreme point `E`, the first moment the
color-difference count becomes `1` gives a balancing line through `E`. -/
lemma sweep {n : ℕ} (_hn : 1 < n) (point : Fin (2 * n) → ℝ × ℝ)
    (color : Fin (2 * n) → Bool)
    (hred : (Finset.univ.filter fun i ↦ color i = true).card = n)
    (hnc : ∀ i j k : Fin (2 * n), i ≠ j → j ≠ k → i ≠ k →
      cross (point j - point i) (point k - point i) ≠ 0)
    (E : Fin (2 * n)) (hE : Extreme point E) :
    ∃ b r : Fin (2 * n), color b = false ∧ color r = true ∧
      (b = E ∨ r = E) ∧ Balancing point color b r := by
  classical
  obtain ⟨d₀, hd₀⟩ := hE
  have hblue := blue_card color hred
  -- the angular order around `E`
  set T := {j : Fin (2 * n) // j ≠ E} with hT
  set r : T → T → Prop := fun j k ↦
    0 ≤ cross (point j.val - point E) (point k.val - point E) with hr
  have hne : ∀ j k : T, j ≠ k →
      cross (point j.val - point E) (point k.val - point E) ≠ 0 := by
    intro j k hjk
    exact hnc E j.val k.val j.prop.symm (fun h ↦ hjk (Subtype.ext h)) k.prop.symm
  haveI : IsTrans T r := ⟨fun a b c hab hbc ↦ by
    change 0 ≤ cross (point a.val - point E) (point c.val - point E)
    by_cases hab' : a = b
    · subst hab'; exact hbc
    · by_cases hbc' : b = c
      · subst hbc'; exact hab
      · by_cases hac' : a = c
        · subst hac'; exact le_of_eq (cross_self _).symm
        · have h1 : 0 < cross (point a.val - point E) (point b.val - point E) :=
            lt_of_le_of_ne hab (hne a b hab').symm
          have h2 : 0 < cross (point b.val - point E) (point c.val - point E) :=
            lt_of_le_of_ne hbc (hne b c hbc').symm
          exact le_of_lt (cross_trans (hd₀ a.val a.prop) (hd₀ b.val b.prop) (hd₀ c.val c.prop)
            h1 h2)⟩
  haveI : Std.Antisymm r := ⟨fun a b hab hba ↦ by
    by_contra hne'
    have hab' : (0:ℝ) ≤ cross (point a.val - point E) (point b.val - point E) := hab
    have hba' : (0:ℝ) ≤ cross (point b.val - point E) (point a.val - point E) := hba
    have h1 := cross_anti (point b.val - point E) (point a.val - point E)
    exact hne a b hne' (by linarith [hab', hba', h1.le])⟩
  haveI : Std.Total r := ⟨fun a b ↦ by
    by_cases hab : a = b
    · subst hab; left; exact le_of_eq (cross_self _).symm
    · have h0 := hne a b hab
      rcases le_total (cross (point a.val - point E) (point b.val - point E)) 0 with h | h
      · right
        change (0:ℝ) ≤ cross (point b.val - point E) (point a.val - point E)
        rw [cross_anti]
        linarith [h]
      · left; exact h⟩
  set L := Finset.sort Finset.univ r with hL
  have hLlen : L.length = 2 * n - 1 := by
    rw [hL, Finset.length_sort, Finset.card_univ, Fintype.card_subtype_compl,
      Fintype.card_subtype_eq, Fintype.card_fin]
  have hLsorted : L.Pairwise r := by rw [hL]; exact Finset.pairwise_sort _ _
  have hLnodup : L.Nodup := by rw [hL]; exact Finset.sort_nodup _ _
  have hLmem : ∀ j : T, j ∈ L := fun j ↦ by rw [hL]; exact (Finset.mem_sort r).mpr (Finset.mem_univ j)
  -- the signed color count
  set val : Fin (2 * n) → ℤ := fun j ↦ if color j = color E then -1 else 1 with hval
  have hvalE : val E = -1 := by simp [hval]
  have hvalpm : ∀ j, val j = 1 ∨ val j = -1 := by
    intro j
    by_cases h : color j = color E
    · right; simp [hval, h]
    · left; simp [hval, h]
  have hsum : ∑ j : Fin (2 * n), val j = 0 := by
    by_cases hE' : color E = true
    · have hc1 : (Finset.univ.filter fun j ↦ color j = color E) =
          (Finset.univ.filter fun j ↦ color j = true) :=
        Finset.filter_congr (fun x _ ↦ by rw [hE'])
      have hc2 : (Finset.univ.filter fun j ↦ ¬ color j = color E) =
          (Finset.univ.filter fun j ↦ color j = false) :=
        Finset.filter_congr (fun x _ ↦ by rw [hE', Bool.not_eq_true])
      have h := Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset (Fin (2 * n))))
        (p := fun j ↦ color j = color E) (f := val)
      rw [hc1, hc2] at h
      have hv1 : ∑ j ∈ Finset.univ.filter (fun j ↦ color j = true), val j = -(n : ℤ) := by
        have e : ∑ j ∈ Finset.univ.filter (fun j ↦ color j = true), val j =
            ∑ j ∈ Finset.univ.filter (fun j ↦ color j = true), (-1 : ℤ) :=
          Finset.sum_congr rfl (fun x hx ↦ by
            have h1 : color x = true := (Finset.mem_filter.mp hx).2
            simp [hval, h1, hE'])
        rw [e, Finset.sum_const, hred, nsmul_eq_mul]
        ring
      have hv2 : ∑ j ∈ Finset.univ.filter (fun j ↦ color j = false), val j = (n : ℤ) := by
        have e : ∑ j ∈ Finset.univ.filter (fun j ↦ color j = false), val j =
            ∑ j ∈ Finset.univ.filter (fun j ↦ color j = false), (1 : ℤ) :=
          Finset.sum_congr rfl (fun x hx ↦ by
            have h1 : color x = false := (Finset.mem_filter.mp hx).2
            simp [hval, h1, hE'])
        rw [e, Finset.sum_const, hblue, nsmul_eq_mul]
        ring
      rw [← h, hv1, hv2]
      exact neg_add_cancel _
    · have hE' : color E = false := (Bool.not_eq_true _).mp ‹¬ color E = true›
      have hc1 : (Finset.univ.filter fun j ↦ color j = color E) =
          (Finset.univ.filter fun j ↦ color j = false) :=
        Finset.filter_congr (fun x _ ↦ by rw [hE'])
      have hc2 : (Finset.univ.filter fun j ↦ ¬ color j = color E) =
          (Finset.univ.filter fun j ↦ color j = true) :=
        Finset.filter_congr (fun x _ ↦ by rw [hE']; cases color x <;> simp)
      have h := Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset (Fin (2 * n))))
        (p := fun j ↦ color j = color E) (f := val)
      rw [hc1, hc2] at h
      have hv1 : ∑ j ∈ Finset.univ.filter (fun j ↦ color j = false), val j = -(n : ℤ) := by
        have e : ∑ j ∈ Finset.univ.filter (fun j ↦ color j = false), val j =
            ∑ j ∈ Finset.univ.filter (fun j ↦ color j = false), (-1 : ℤ) :=
          Finset.sum_congr rfl (fun x hx ↦ by
            have h1 : color x = false := (Finset.mem_filter.mp hx).2
            simp [hval, h1, hE'])
        rw [e, Finset.sum_const, hblue, nsmul_eq_mul]
        ring
      have hv2 : ∑ j ∈ Finset.univ.filter (fun j ↦ color j = true), val j = (n : ℤ) := by
        have e : ∑ j ∈ Finset.univ.filter (fun j ↦ color j = true), val j =
            ∑ j ∈ Finset.univ.filter (fun j ↦ color j = true), (1 : ℤ) :=
          Finset.sum_congr rfl (fun x hx ↦ by
            have h1 : color x = true := (Finset.mem_filter.mp hx).2
            simp [hval, h1, hE'])
        rw [e, Finset.sum_const, hred, nsmul_eq_mul]
        ring
      rw [← h, hv1, hv2]
      exact neg_add_cancel _
  have hsumL : (L.map fun j : T ↦ val j.val).sum = 1 := by
    have e1 : (L.map fun j : T ↦ val j.val).sum = ∑ j : T, val j.val := by
      rw [← List.sum_toFinset (fun j : T ↦ val j.val) hLnodup, hL, Finset.sort_toFinset]
    have e2 : ∑ j : T, val j.val = ∑ j ∈ Finset.univ.erase E, val j := by
      have h : ∑ a ∈ Finset.univ.erase E, val a = ∑ a : {x // x ≠ E}, val a.val :=
        Finset.sum_subtype (Finset.univ.erase E)
          (fun x ↦ Finset.mem_erase.trans (and_iff_left (Finset.mem_univ x))) val
      exact h.symm
    have e3 : ∑ j ∈ Finset.univ.erase E, val j = 1 := by
      have h := Finset.sum_erase_add (Finset.univ : Finset (Fin (2 * n))) val (Finset.mem_univ E)
      rw [hsum, hvalE] at h
      linarith [h]
    rw [e1, e2, e3]
  -- the walk
  set G : ℕ → ℤ := fun m ↦ ((L.take m).map fun j : T ↦ val j.val).sum with hG
  have hG0 : G 0 = 0 := by simp [hG]
  have hGtot : G (2 * n - 1) = 1 := by
    show ((L.take (2 * n - 1)).map fun j : T ↦ val j.val).sum = 1
    rw [List.take_of_length_le (le_of_eq hLlen)]
    exact hsumL
  have hstep : ∀ m : ℕ, ∀ hm : m < L.length, G (m + 1) = G m + val (L.get ⟨m, hm⟩) := by
    intro m hmlen
    have e : L.take (m + 1) = L.take m ++ [L.get ⟨m, hmlen⟩] := (List.take_append_getElem hmlen).symm
    show ((L.take (m + 1)).map fun j : T ↦ val j.val).sum =
      ((L.take m).map fun j : T ↦ val j.val).sum + val (L.get ⟨m, hmlen⟩)
    rw [e, List.map_append, List.sum_append]
    simp
  have ivt : ∀ t : ℕ, t + 1 ≤ 2 * n - 1 → 1 ≤ G t → ∃ k ≤ t, G k = 1 := by
    intro t
    induction t with
    | zero => intro _ ht; rw [hG0] at ht; omega
    | succ t ih =>
      intro ht1 ht2
      by_cases h : 1 ≤ G t
      · obtain ⟨k, hk1, hk2⟩ := ih (by omega) h
        exact ⟨k, by omega, hk2⟩
      · push Not at h
        have hs := hstep t (by rw [hLlen]; omega)
        obtain hv | hv := hvalpm (L.get ⟨t, by rw [hLlen]; omega⟩)
        · exact ⟨t + 1, le_refl _, by linarith [hs, hv, h, ht2]⟩
        · exfalso
          linarith [hs, hv, h, ht2]
  -- the critical index
  have hex : ∃ m, G m = 1 := ⟨2 * n - 1, hGtot⟩
  set mstar := Nat.find hex with hmstar
  have hm1 : G mstar = 1 := Nat.find_spec hex
  have hmmin : ∀ k, k < mstar → ¬ G k = 1 := fun k hk ↦ Nat.find_min hex hk
  have hmle : mstar ≤ 2 * n - 1 := Nat.find_le (h := hex) hGtot
  have hm0 : mstar ≠ 0 := by
    intro h
    rw [h, hG0] at hm1
    omega
  set m0 := mstar - 1 with hm0def
  have hm0eq : m0 + 1 = mstar := by
    rw [hm0def]
    omega
  have hmlen0 : m0 < L.length := by rw [hLlen]; omega
  set t₀ := L.get ⟨m0, hmlen0⟩ with ht₀
  set j₀ := t₀.val with hj₀
  have hj₀E : j₀ ≠ E := t₀.prop
  have hGstep : G (m0 + 1) = G m0 + val t₀.val := hstep m0 (by omega)
  have hGm0 : G m0 = 0 := by
    obtain hv | hv := hvalpm t₀.val
    · rw [hm0eq, hm1] at hGstep
      linarith [hGstep, hv]
    · rw [hm0eq, hm1] at hGstep
      have h2 : G m0 = 2 := by linarith [hGstep, hv]
      obtain ⟨k, hk1, hk2⟩ := ivt m0 (by omega) (by rw [h2]; norm_num)
      have hkm : k < mstar := by omega
      exact False.elim (hmmin k hkm hk2)
  have hvalj₀ : val j₀ = 1 := by
    have h := hGstep
    rw [hm0eq, hm1, hGm0] at h
    have h2 : val t₀.val = 1 := by linarith [h]
    exact h2
  -- list decomposition at the critical index
  have hw : L = L.take m0 ++ (t₀ :: L.drop (m0 + 1)) := by
    have e1 : L = L.take (m0 + 1) ++ L.drop (m0 + 1) := (List.take_append_drop (m0 + 1) L).symm
    have e2 : L.take (m0 + 1) = L.take m0 ++ [t₀] := (List.take_append_getElem hmlen0).symm
    conv_lhs => rw [e1, e2]
    rw [List.append_assoc, List.singleton_append]
  have ht₀mem1 : t₀ ∈ L.take (m0 + 1) := by
    rw [← List.take_append_getElem (l := L) (i := m0) hmlen0]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  have ht₀mem2 : t₀ ∈ L.drop m0 := by
    rw [← List.getElem_cons_drop (as := L) (i := m0) hmlen0]
    exact List.Mem.head _
  have hpair1 : ∀ x ∈ L.take m0, ∀ y ∈ t₀ :: L.drop (m0 + 1), r x y := by
    have hpair := hLsorted
    rw [hw, List.pairwise_append] at hpair
    exact hpair.2.2
  have hpair2 : ∀ x ∈ L.take (m0 + 1), ∀ y ∈ L.drop (m0 + 1), r x y := by
    have hpair := hLsorted
    rw [← List.take_append_drop (m0 + 1) L, List.pairwise_append] at hpair
    exact hpair.2.2
  have hpair3 : ∀ y ∈ L.drop (m0 + 1), r t₀ y := by
    have hsub : (L.drop m0).Pairwise r := List.Pairwise.sublist (List.drop_sublist m0 L) hLsorted
    rw [← List.getElem_cons_drop (as := L) (i := m0) hmlen0, List.pairwise_cons] at hsub
    exact hsub.1
  have hneTD : ∀ a ∈ L.take (m0 + 1), ∀ b ∈ L.drop (m0 + 1), a ≠ b := by
    have h := hLnodup
    rw [← List.take_append_drop (m0 + 1) L, List.nodup_append] at h
    exact h.2.2
  have hneTD' : ∀ a ∈ L.take m0, ∀ b ∈ t₀ :: L.drop (m0 + 1), a ≠ b := by
    have h := hLnodup
    rw [hw, List.nodup_append] at h
    exact h.2.2
  have hnodTake : (L.take m0).Nodup := by
    have h := hLnodup
    rw [hw, List.nodup_append] at h
    exact h.1
  have hnodDrop : (L.drop (m0 + 1)).Nodup := by
    have h := hLnodup
    rw [← List.take_append_drop (m0 + 1) L, List.nodup_append] at h
    exact h.2.1
  -- the two sides of the line through `E` and `j₀`
  have hSplus : Finset.univ.filter (fun k ↦ 0 < cross (point j₀ - point E) (point k - point E))
      = ((L.drop (m0 + 1)).map Subtype.val).toFinset := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.mem_toFinset, List.mem_map]
    constructor
    · intro hk
      have hkE : k ≠ E := by
        intro h
        subst h
        rw [sub_self, cross_zero_right] at hk
        exact lt_irrefl 0 hk
      refine ⟨⟨k, hkE⟩, ?_, rfl⟩
      have hmem := hLmem ⟨k, hkE⟩
      rw [← List.take_append_drop (m0 + 1) L, List.mem_append] at hmem
      rcases hmem with h | h
      · rw [← List.take_append_getElem (l := L) (i := m0) hmlen0, List.mem_append] at h
        rcases h with h | h
        · exfalso
          have hr1 := hpair1 _ h t₀ (List.Mem.head _)
          have hr1' : (0:ℝ) ≤ cross (point k - point E) (point j₀ - point E) := hr1
          have hanti := cross_anti (point k - point E) (point j₀ - point E)
          linarith [hk, hr1', hanti.le]
        · have h2 : (⟨k, hkE⟩ : T) = t₀ := List.mem_singleton.mp h
          have h3 : k = j₀ := congrArg Subtype.val h2
          subst h3
          rw [cross_self] at hk
          exact False.elim (lt_irrefl 0 hk)
      · exact h
    · rintro ⟨t, ht, rfl⟩
      have hr2 := hpair2 t₀ ht₀mem1 t ht
      have hne2 : t₀ ≠ t := hneTD t₀ ht₀mem1 t ht
      have hne2' : cross (point t₀.val - point E) (point t.val - point E) ≠ 0 := hne t₀ t hne2
      have hr2' : (0:ℝ) ≤ cross (point t₀.val - point E) (point t.val - point E) := hr2
      exact lt_of_le_of_ne hr2' hne2'.symm
  have hSminus : Finset.univ.filter (fun k ↦ cross (point j₀ - point E) (point k - point E) < 0)
      = ((L.take m0).map Subtype.val).toFinset := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.mem_toFinset, List.mem_map]
    constructor
    · intro hk
      have hkE : k ≠ E := by
        intro h
        subst h
        rw [sub_self, cross_zero_right] at hk
        exact lt_irrefl 0 hk
      refine ⟨⟨k, hkE⟩, ?_, rfl⟩
      have hmem := hLmem ⟨k, hkE⟩
      rw [← List.take_append_drop m0 L, List.mem_append] at hmem
      rcases hmem with h | h
      · exact h
      · rw [← List.getElem_cons_drop (as := L) (i := m0) hmlen0, List.mem_cons] at h
        rcases h with h | h
        · have h3 : k = j₀ := congrArg Subtype.val h
          subst h3
          rw [cross_self] at hk
          exact False.elim (lt_irrefl 0 hk)
        · exfalso
          have hr3 := hpair3 _ h
          have hr3' : (0:ℝ) ≤ cross (point j₀ - point E) (point k - point E) := hr3
          linarith [hk, hr3']
    · rintro ⟨t, ht, rfl⟩
      have hr1 := hpair1 t ht t₀ (List.Mem.head _)
      have hne2 : t ≠ t₀ := hneTD' t ht t₀ (List.Mem.head _)
      have hne2' : cross (point t.val - point E) (point t₀.val - point E) ≠ 0 := hne t t₀ hne2
      have hr1' : (0:ℝ) ≤ cross (point t.val - point E) (point t₀.val - point E) := hr1
      have hpos : 0 < cross (point t.val - point E) (point t₀.val - point E) :=
        lt_of_le_of_ne hr1' hne2'.symm
      have e := cross_anti (point t₀.val - point E) (point t.val - point E)
      show cross (point t₀.val - point E) (point t.val - point E) < 0
      linarith [hpos, e.le]
  -- count sums over the two sides
  have hdrop : ((L.drop (m0 + 1)).map fun j : T ↦ val j.val).sum = 0 := by
    have h1 : (L.map fun j : T ↦ val j.val).sum =
        ((L.take (m0 + 1)).map fun j : T ↦ val j.val).sum +
        ((L.drop (m0 + 1)).map fun j : T ↦ val j.val).sum := by
      conv_lhs => rw [← List.take_append_drop (m0 + 1) L, List.map_append, List.sum_append]
    have h2 : ((L.take (m0 + 1)).map fun j : T ↦ val j.val).sum = 1 := by
      have h : G (m0 + 1) = 1 := by rw [hm0eq]; exact hm1
      exact h
    linarith [hsumL, h1, h2]
  have htake : ((L.take m0).map fun j : T ↦ val j.val).sum = 0 := hGm0
  have hsumP : ∑ k ∈ (Finset.univ.filter fun k ↦
      0 < cross (point j₀ - point E) (point k - point E)), val k = 0 := by
    rw [hSplus, List.sum_toFinset val (List.Nodup.map Subtype.val_injective hnodDrop),
      List.map_map]
    simpa only [Function.comp_def] using hdrop
  have hsumM : ∑ k ∈ (Finset.univ.filter fun k ↦
      cross (point j₀ - point E) (point k - point E) < 0), val k = 0 := by
    rw [hSminus, List.sum_toFinset val (List.Nodup.map Subtype.val_injective hnodTake),
      List.map_map]
    simpa only [Function.comp_def] using htake
  -- from sums to cardinalities
  have hcard_eq : ∀ S : Finset (Fin (2 * n)), ∑ k ∈ S, val k = 0 →
      (S.filter fun k ↦ ¬ color k = color E).card = (S.filter fun k ↦ color k = color E).card := by
    intro S hS
    have hsplit := Finset.sum_filter_add_sum_filter_not (s := S) (p := fun k ↦ color k = color E)
      (f := val)
    have e1 : ∑ k ∈ S.filter (fun k ↦ color k = color E), val k =
        -((S.filter fun k ↦ color k = color E).card : ℤ) := by
      have e : ∑ k ∈ S.filter (fun k ↦ color k = color E), val k =
          ∑ k ∈ S.filter (fun k ↦ color k = color E), (-1 : ℤ) :=
        Finset.sum_congr rfl (fun x hx ↦ by
          have h1 : color x = color E := (Finset.mem_filter.mp hx).2
          simp [hval, h1])
      rw [e, Finset.sum_const, nsmul_eq_mul]
      ring
    have e2 : ∑ k ∈ S.filter (fun k ↦ ¬ color k = color E), val k =
        ((S.filter fun k ↦ ¬ color k = color E).card : ℤ) := by
      have e : ∑ k ∈ S.filter (fun k ↦ ¬ color k = color E), val k =
          ∑ k ∈ S.filter (fun k ↦ ¬ color k = color E), (1 : ℤ) :=
        Finset.sum_congr rfl (fun x hx ↦ by
          have h1 : ¬ color x = color E := (Finset.mem_filter.mp hx).2
          simp [hval, h1])
      rw [e, Finset.sum_const, nsmul_eq_mul]
      ring
    rw [← hsplit, e1, e2] at hS
    have h : ((S.filter fun k ↦ ¬ color k = color E).card : ℤ) =
        ((S.filter fun k ↦ color k = color E).card : ℤ) := by linarith [hS]
    exact Nat.cast_injective h
  have hplus := hcard_eq _ hsumP
  have hminus := hcard_eq _ hsumM
  -- assemble the balancing pair
  by_cases hEc : color E = true
  · -- `E` is red, `j₀` is blue
    have hj₀c : color j₀ = false := by
      by_contra h
      have h1 : color j₀ = color E := by rw [(Bool.not_eq_false _).mp h, hEc]
      simp [hval, h1] at hvalj₀
    refine ⟨j₀, E, hj₀c, hEc, Or.inr rfl, ?_⟩
    have hside : ∀ k, cross (point E - point j₀) (point k - point j₀) =
        -cross (point j₀ - point E) (point k - point E) := by
      intro k
      have e1 : point k - point j₀ = (point k - point E) + (point E - point j₀) :=
        Prod.ext (by show (point k).1 - (point j₀).1 =
            (point k).1 - (point E).1 + ((point E).1 - (point j₀).1); ring)
          (by show (point k).2 - (point j₀).2 =
            (point k).2 - (point E).2 + ((point E).2 - (point j₀).2); ring)
      have e2 : point E - point j₀ = -(point j₀ - point E) :=
        Prod.ext (by show (point E).1 - (point j₀).1 = -((point j₀).1 - (point E).1); ring)
          (by show (point E).2 - (point j₀).2 = -((point j₀).2 - (point E).2); ring)
      rw [e1, cross_add_right, e2, cross_neg_left, cross_self, add_zero]
    refine ⟨?_, ?_⟩
    · have e1 : (Finset.univ.filter fun k ↦
          0 < cross (point E - point j₀) (point k - point j₀) ∧ color k = true) =
          (Finset.univ.filter fun k ↦
            cross (point j₀ - point E) (point k - point E) < 0).filter
            (fun k ↦ color k = color E) := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        apply Iff.and
        · rw [hside]; exact neg_pos
        · rw [hEc]
      have e2 : (Finset.univ.filter fun k ↦
          0 < cross (point E - point j₀) (point k - point j₀) ∧ color k = false) =
          (Finset.univ.filter fun k ↦
            cross (point j₀ - point E) (point k - point E) < 0).filter
            (fun k ↦ ¬ color k = color E) := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        apply Iff.and
        · rw [hside]; exact neg_pos
        · rw [hEc]; cases color k <;> simp
      rw [e1, e2]
      exact hminus.symm
    · have e1 : (Finset.univ.filter fun k ↦
          cross (point E - point j₀) (point k - point j₀) < 0 ∧ color k = true) =
          (Finset.univ.filter fun k ↦
            0 < cross (point j₀ - point E) (point k - point E)).filter
            (fun k ↦ color k = color E) := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        apply Iff.and
        · rw [hside]; exact neg_lt_zero
        · rw [hEc]
      have e2 : (Finset.univ.filter fun k ↦
          cross (point E - point j₀) (point k - point j₀) < 0 ∧ color k = false) =
          (Finset.univ.filter fun k ↦
            0 < cross (point j₀ - point E) (point k - point E)).filter
            (fun k ↦ ¬ color k = color E) := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        apply Iff.and
        · rw [hside]; exact neg_lt_zero
        · rw [hEc]; cases color k <;> simp
      rw [e1, e2]
      exact hplus.symm
  · -- `E` is blue, `j₀` is red
    have hEc' : color E = false := (Bool.not_eq_true _).mp hEc
    have hj₀c : color j₀ = true := by
      by_contra h
      have h1 : color j₀ = color E := by rw [(Bool.not_eq_true _).mp h, hEc']
      simp [hval, h1] at hvalj₀
    refine ⟨E, j₀, hEc', hj₀c, Or.inl rfl, ?_⟩
    refine ⟨?_, ?_⟩
    · have e1 : (Finset.univ.filter fun k ↦
          0 < cross (point j₀ - point E) (point k - point E) ∧ color k = true) =
          (Finset.univ.filter fun k ↦
            0 < cross (point j₀ - point E) (point k - point E)).filter
            (fun k ↦ ¬ color k = color E) := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        apply Iff.and
        · exact Iff.rfl
        · rw [hEc']; cases color k <;> simp
      have e2 : (Finset.univ.filter fun k ↦
          0 < cross (point j₀ - point E) (point k - point E) ∧ color k = false) =
          (Finset.univ.filter fun k ↦
            0 < cross (point j₀ - point E) (point k - point E)).filter
            (fun k ↦ color k = color E) := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        apply Iff.and
        · exact Iff.rfl
        · rw [hEc']
      rw [e1, e2]
      exact hplus
    · have e1 : (Finset.univ.filter fun k ↦
          cross (point j₀ - point E) (point k - point E) < 0 ∧ color k = true) =
          (Finset.univ.filter fun k ↦
            cross (point j₀ - point E) (point k - point E) < 0).filter
            (fun k ↦ ¬ color k = color E) := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        apply Iff.and
        · exact Iff.rfl
        · rw [hEc']; cases color k <;> simp
      have e2 : (Finset.univ.filter fun k ↦
          cross (point j₀ - point E) (point k - point E) < 0 ∧ color k = false) =
          (Finset.univ.filter fun k ↦
            cross (point j₀ - point E) (point k - point E) < 0).filter
            (fun k ↦ color k = color E) := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        apply Iff.and
        · exact Iff.rfl
        · rw [hEc']
      rw [e1, e2]
      exact hminus

snip end

problem usa2005_p5 {n : ℕ} (hn : 1 < n) (point : Fin (2 * n) → ℝ × ℝ)
    (color : Fin (2 * n) → Bool)
    (hred : (Finset.univ.filter fun i ↦ color i = true).card = n)
    (hnc : ∀ i j k : Fin (2 * n), i ≠ j → j ≠ k → i ≠ k →
      cross (point j - point i) (point k - point i) ≠ 0) :
    ∃ b₁ r₁ b₂ r₂ : Fin (2 * n),
      color b₁ = false ∧ color r₁ = true ∧ color b₂ = false ∧ color r₂ = true ∧
      (b₁, r₁) ≠ (b₂, r₂) ∧ Balancing point color b₁ r₁ ∧ Balancing point color b₂ r₂ := by
  classical
  have h2n : 0 < 2 * n := by omega
  have hinj : Function.Injective point := injective_of_hnc hn point hnc
  obtain ⟨A, hAE, hA1, -⟩ := exists_extreme_lexmax point hinj h2n
  obtain ⟨B, hBE, hB1, -⟩ := exists_extreme_lexmin point hinj h2n
  have hAB : A ≠ B := by
    intro h
    subst h
    have hsame : ∀ j, (point j).1 = (point A).1 := fun j ↦ le_antisymm (hA1 j) (hB1 j)
    obtain ⟨i, j, k, hij, hjk, hik⟩ : ∃ i j k : Fin (2 * n), i ≠ j ∧ j ≠ k ∧ i ≠ k :=
      ⟨⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩, by simp, by simp, by simp⟩
    apply hnc i j k hij hjk hik
    have e1 : (point j - point i).1 = 0 := sub_eq_zero.mpr ((hsame j).trans (hsame i).symm)
    have e2 : (point k - point i).1 = 0 := sub_eq_zero.mpr ((hsame k).trans (hsame i).symm)
    show (point j - point i).1 * (point k - point i).2 -
      (point j - point i).2 * (point k - point i).1 = 0
    rw [e1, e2]
    ring
  obtain ⟨j₀, hj₀A, hj₀B⟩ : ∃ j, j ≠ A ∧ j ≠ B := exists_ne_two hn A B
  obtain ⟨C, hCE, hCA, hCB⟩ :=
    exists_third_extreme point hinj hAB ⟨j₀, hnc A B j₀ hAB hj₀B.symm hj₀A.symm⟩
  obtain ⟨b₁, r₁, hb₁, hr₁, hE₁, hBal₁⟩ := sweep hn point color hred hnc A hAE
  obtain ⟨b₂, r₂, hb₂, hr₂, hE₂, hBal₂⟩ := sweep hn point color hred hnc B hBE
  obtain ⟨b₃, r₃, hb₃, hr₃, hE₃, hBal₃⟩ := sweep hn point color hred hnc C hCE
  -- the three pairs cannot all coincide (three distinct extreme points, two slots)
  have hne : (b₁, r₁) ≠ (b₂, r₂) ∨ (b₁, r₁) ≠ (b₃, r₃) ∨ (b₂, r₂) ≠ (b₃, r₃) := by
    by_contra! h
    obtain ⟨h12, h13, -⟩ := h
    have hbr : b₁ ≠ r₁ := by
      intro h'
      rw [h'] at hb₁
      rw [hb₁] at hr₁
      exact Bool.false_ne_true hr₁
    have hmemA : A = b₁ ∨ A = r₁ := hE₁.elim (fun h' ↦ Or.inl h'.symm) (fun h' ↦ Or.inr h'.symm)
    have hB2 : B = b₁ ∨ B = r₁ := by
      rcases hE₂ with h' | h'
      · exact Or.inl (h'.symm.trans (Prod.mk.inj h12).1.symm)
      · exact Or.inr (h'.symm.trans (Prod.mk.inj h12).2.symm)
    have hC2 : C = b₁ ∨ C = r₁ := by
      rcases hE₃ with h' | h'
      · exact Or.inl (h'.symm.trans (Prod.mk.inj h13).1.symm)
      · exact Or.inr (h'.symm.trans (Prod.mk.inj h13).2.symm)
    rcases hmemA with rfl | rfl
    · rcases hB2 with h' | h'
      · exact hAB h'.symm
      · rcases hC2 with h'' | h''
        · exact hCA h''
        · exact hCB (h''.trans h'.symm)
    · rcases hB2 with h' | h'
      · rcases hC2 with h'' | h''
        · exact hCB (h''.trans h'.symm)
        · exact hCA h''
      · exact hAB h'.symm
  rcases hne with h | h | h
  · exact ⟨b₁, r₁, b₂, r₂, hb₁, hr₁, hb₂, hr₂, h, hBal₁, hBal₂⟩
  · exact ⟨b₁, r₁, b₃, r₃, hb₁, hr₁, hb₃, hr₃, h, hBal₁, hBal₃⟩
  · exact ⟨b₂, r₂, b₃, r₃, hb₂, hr₂, hb₃, hr₃, h, hBal₂, hBal₃⟩

end Usa2005P5
