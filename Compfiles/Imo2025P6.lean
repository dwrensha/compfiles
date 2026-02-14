/-
Copyright (c) 2026 lean-tom. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-tom (with assistance from Gemini)
-/

import Mathlib.Analysis.MeanInequalities
import Archive.Wiedijk100Theorems.AscendingDescendingSequences
import ProblemExtraction

open Finset Function

problem_file

/-!
# International Mathematical Olympiad 2025, Problem 6

Consider a 2025 × 2025 grid of unit squares. Matilda wishes to place
on the grid some rectangular tiles, possibly of different sizes,
such that each side of every tile lies on a grid line and
every unit square is covered by at most one tile.
Determine the minimum number of tiles Matilda needs to place
so that each row and each column of the grid has exactly one unit square
that is not covered by any tile.
-/

namespace Imo2025P6

section ProblemSetup

variable {n : ℕ} [NeZero n]

/-- A square in the n x n grid. -/
abbrev Point (n : ℕ) := Fin n × Fin n
abbrev px (p : Point n) : ℕ := p.1.val
abbrev py (p : Point n) : ℕ := p.2.val
variable {all_black : Finset (Point n)}
/-- A rectangular tile that does not cover any of the specified black squares. -/
structure Matilda (n : ℕ) [NeZero n] (all_black : Finset (Point n)) where
  x_min : ℕ
  x_max : ℕ
  y_min : ℕ
  y_max : ℕ
  h_x_le : x_min ≤ x_max
  h_y_le : y_min ≤ y_max
  h_x_bound : x_max < n
  h_y_bound : y_max < n
  h_disjoint : ∀ p ∈ all_black, ¬(x_min ≤ px p ∧ px p ≤ x_max ∧ y_min ≤ py p ∧ py p ≤ y_max)
@[simp]
def Matilda.mem (m : Matilda n all_black) (p : Point n) : Prop :=
  m.x_min ≤ px p ∧ px p ≤ m.x_max ∧ m.y_min ≤ py p ∧ py p ≤ m.y_max

/-- Configuration where each row/column has exactly one uncovered square (all_black). -/
def IsValidConfiguration (n : ℕ) [NeZero n]
  (all_black : Finset (Point n)) (partition : Finset (Matilda n all_black)) : Prop :=
  all_black.card = n ∧
  (∀ p ∈ all_black, ∀ q ∈ all_black, px p = px q → p = q) ∧
  (∀ p ∈ all_black, ∀ q ∈ all_black, py p = py q → p = q) ∧
  (∀ p : Point n, p ∉ all_black → ∃! m ∈ partition, m.mem p)

/-- The minimum number of tiles needed across all valid black square sets. -/
def IsMinMatildaCount (n : ℕ) [NeZero n] (m : ℕ) : Prop :=
  (∀ (all_black : Finset (Point n)) (partition : Finset (Matilda n all_black)),
      IsValidConfiguration n all_black partition → m ≤ partition.card) ∧
  (∃ (all_black : Finset (Point n)) (partition : Finset (Matilda n all_black)),
      IsValidConfiguration n all_black partition ∧ partition.card = m)

end ProblemSetup

snip begin

instance px_refl : @Std.Refl (Point n) ((· ≤ ·) on px) := ⟨fun _ => le_refl _⟩
instance py_refl : @Std.Refl (Point n) ((· ≤ ·) on py) := ⟨fun _ => le_refl _⟩
def rect (n : ℕ) (x_min x_max y_min y_max : ℕ) : Finset (Point n) :=
  univ.filter (fun p =>
    x_min ≤ px p ∧ px p < x_max ∧
    y_min ≤ py p ∧ py p < y_max
  )

@[simp]
lemma mem_rect {x_min x_max y_min y_max : ℕ} {p : Point n} :
    p ∈ rect n x_min x_max y_min y_max ↔
    x_min ≤ px p ∧ px p < x_max ∧
    y_min ≤ py p ∧ py p < y_max := by
  simp [rect]
syntax "contradict_max" term "using" term "as" ident ident ident : tactic

macro_rules
  | `(tactic| contradict_max $max_hyp:term using $not_mem:term as $q:ident $hq:ident $h_ord:ident) =>
    `(tactic| apply ($max_hyp) _ ($not_mem) <;> intro $q $hq $h_ord)

macro "solve_grid" : tactic =>
  `(tactic| (
    simp only [Fin.le_iff_val_le_val, px, py] at *
    linarith
  ))

section CommonProperties

variable {all_black : Finset (Point n)}

lemma eq_of_px_eq
    (h_unique_x : ∀ p ∈ all_black, ∀ q ∈ all_black, px p = px q → p = q)
    {p q : Point n} (hp : p ∈ all_black) (hq : q ∈ all_black)
    (h_eq : px p = px q) : p = q :=
  h_unique_x p hp q hq h_eq
lemma eq_of_py_eq
    (h_unique_y : ∀ p ∈ all_black, ∀ q ∈ all_black, py p = py q → p = q)
    {p q : Point n} (hp : p ∈ all_black) (hq : q ∈ all_black)
    (h_eq : py p = py q) : p = q :=
  h_unique_y p hp q hq h_eq

end CommonProperties

section ChainProperties

variable {u v : Finset (Point n)}

lemma chain_u_mono_le
    (h_u_mono : ∀ a ∈ u, ∀ b ∈ u, px a < px b → py a < py b)
    (h_u_inj : ∀ a ∈ u, ∀ b ∈ u, px a = px b → a = b)
    : ∀ a ∈ u, ∀ b ∈ u, px a ≤ px b → py a ≤ py b := by
  intro a ha b hb hx
  rcases lt_or_eq_of_le hx with h_lt | h_eq
  · exact le_of_lt (h_u_mono a ha b hb h_lt)
  · have := h_u_inj a ha b hb h_eq; subst this; exact le_refl _

lemma chain_v_mono_le
    (h_v_mono : ∀ a ∈ v, ∀ b ∈ v, px a < px b → py b < py a)
    (h_v_inj : ∀ a ∈ v, ∀ b ∈ v, px a = px b → a = b)
    : ∀ a ∈ v, ∀ b ∈ v, px a ≤ px b → py b ≤ py a := by
  intro a ha b hb hx
  rcases lt_or_eq_of_le hx with h_lt | h_eq
  · exact le_of_lt (h_v_mono a ha b hb h_lt)
  · have := h_v_inj a ha b hb h_eq; subst this; exact le_refl _

lemma chain_u_inj_y
    (h_u_mono : ∀ a ∈ u, ∀ b ∈ u, px a < px b → py a < py b)
    (h_u_inj : ∀ a ∈ u, ∀ b ∈ u, px a = px b → a = b)
    : ∀ a ∈ u, ∀ b ∈ u, py a = py b → a = b := by
  intro a ha b hb hy
  rcases lt_trichotomy (px a) (px b) with h_lt | h_eq | h_gt
  · have := h_u_mono a ha b hb h_lt; linarith
  · exact h_u_inj a ha b hb h_eq
  · have := h_u_mono b hb a ha h_gt; linarith

lemma chain_v_inj_y
    (h_v_mono : ∀ a ∈ v, ∀ b ∈ v, px a < px b → py b < py a)
    (h_v_inj : ∀ a ∈ v, ∀ b ∈ v, px a = px b → a = b)
    : ∀ a ∈ v, ∀ b ∈ v, py a = py b → a = b := by
  intro a ha b hb hy
  rcases lt_trichotomy (px a) (px b) with h_lt | h_eq | h_gt
  · have := h_v_mono a ha b hb h_lt; linarith
  · exact h_v_inj a ha b hb h_eq
  · have := h_v_mono b hb a ha h_gt; linarith

end ChainProperties

section Regions

variable (u v : Finset (Point n))

def u_lower : Finset (Point n) := u.biUnion (fun q => rect n (px q) n 0 ((py q) + 1))
def u_upper : Finset (Point n) := u.biUnion (fun q => rect n 0 ((px q) + 1) (py q) n)
def v_lower : Finset (Point n) := v.biUnion (fun r => rect n 0 ((px r) + 1) 0 ((py r) + 1))
def v_upper : Finset (Point n) := v.biUnion (fun r => rect n (px r) n (py r) n)

@[simp]
lemma mem_u_lower (p : Point n) :
    p ∈ u_lower u ↔ ∃ q ∈ u, px q ≤ px p ∧ py p ≤ py q := by
simp [u_lower, mem_rect]
@[simp]
lemma mem_u_upper (p : Point n) :
    p ∈ u_upper u ↔ ∃ q ∈ u, px p ≤ px q ∧ py q ≤ py p := by
  simp [u_upper, mem_rect]
@[simp]
lemma mem_v_lower (p : Point n) :
    p ∈ v_lower v ↔ ∃ r ∈ v, px p ≤ px r ∧ py p ≤ py r := by
  simp [v_lower, mem_rect]
@[simp]
lemma mem_v_upper (p : Point n) :
    p ∈ v_upper v ↔ ∃ r ∈ v, px r ≤ px p ∧ py r ≤ py p := by
  simp [v_upper, mem_rect]

end Regions

section MainRegions

variable {n : ℕ}  (u v : Finset (Point n)) (all_black : Finset (Point n))

def regionWExtend : Finset (Point n) := (u_lower u) ∩ (v_lower v)
def regionNExtend : Finset (Point n) := (u_upper u) ∩ (v_lower v)
def regionSExtend : Finset (Point n) := (u_lower u) ∩ (v_upper v)
def regionEExtend : Finset (Point n) := (u_upper u) ∩ (v_upper v)

@[simp]
lemma mem_regionWExtend (p : Point n) :
    p ∈ regionWExtend u v ↔ p ∈ u_lower u ∧ p ∈ v_lower v := by unfold regionWExtend; simp
@[simp]
lemma mem_regionNExtend (p : Point n) :
    p ∈ regionNExtend u v ↔ p ∈ u_upper u ∧ p ∈ v_lower v := by unfold regionNExtend; simp
@[simp]
lemma mem_regionSExtend (p : Point n) :
    p ∈ regionSExtend u v ↔ p ∈ u_lower u ∧ p ∈ v_upper v := by unfold regionSExtend; simp
@[simp]
lemma mem_regionEExtend (p : Point n) :
    p ∈ regionEExtend u v ↔ p ∈ u_upper u ∧ p ∈ v_upper v := by unfold regionEExtend; simp

def targetsW (u v all_black : Finset (Point n)) : Finset (Point n) :=
  all_black.filter (fun p => p ∈ regionWExtend u v)
def targetsN (u v all_black : Finset (Point n)) : Finset (Point n) :=
  all_black.filter (fun p => p ∈ regionNExtend u v)
def targetsS (u v all_black : Finset (Point n)) : Finset (Point n) :=
  all_black.filter (fun p => p ∈ regionSExtend u v)
def targetsE (u v all_black : Finset (Point n)) : Finset (Point n) :=
  all_black.filter (fun p => p ∈ regionEExtend u v)

@[simp]
lemma mem_targetsW (p : Point n) :
    p ∈ targetsW u v all_black ↔ p ∈ all_black ∧ p ∈ regionWExtend u v := by
  simp [targetsW]
@[simp]
lemma mem_targetsN (p : Point n) :
    p ∈ targetsN u v all_black ↔ p ∈ all_black ∧ p ∈ regionNExtend u v := by
  simp [targetsN]
@[simp]
lemma mem_targetsS (p : Point n) :
    p ∈ targetsS u v all_black ↔ p ∈ all_black ∧ p ∈ regionSExtend u v := by
  simp [targetsS]
@[simp]
lemma mem_targetsE (p : Point n) :
    p ∈ targetsE u v all_black ↔ p ∈ all_black ∧ p ∈ regionEExtend u v := by
  simp [targetsE]

def targetsWin : Finset (Point n) := (targetsW u v all_black).filter (fun p => 0 < py p)
def targetsNin : Finset (Point n) := (targetsN u v all_black).filter (fun p => 0 < px p)
def targetsSin : Finset (Point n) := (targetsS u v all_black).filter (fun p => px p < n - 1)
def targetsEin : Finset (Point n) := (targetsE u v all_black).filter (fun p => py p < n - 1)

@[simp]
lemma mem_targetsWin {p : Point n} :
    p ∈ targetsWin u v all_black ↔ p ∈ targetsW u v all_black ∧ 0 < py p := by simp [targetsWin]
@[simp]
lemma mem_targetsNin {p : Point n} :
    p ∈ targetsNin u v all_black ↔ p ∈ targetsN u v all_black ∧ 0 < px p := by simp [targetsNin]
@[simp]
lemma mem_targetsSin {p : Point n} :
    p ∈ targetsSin u v all_black ↔ p ∈ targetsS u v all_black ∧ px p < n - 1 := by simp [targetsSin]
@[simp]
lemma mem_targetsEin {p : Point n} :
    p ∈ targetsEin u v all_black ↔ p ∈ targetsE u v all_black ∧ py p < n - 1 := by simp [targetsEin]

lemma card_filter_ge_sub_one {α : Type*} [DecidableEq α]
    (S : Finset α) (P : α → Prop) [DecidablePred P]
    (h_boundary : (S.filter (fun x => ¬ P x)).card ≤ 1) :
    (S.filter P).card ≥ S.card - 1 := by
  have h_card_split : S.card = (S.filter P).card + (S.filter (fun x => ¬ P x)).card := by
    rw [← card_union_of_disjoint (disjoint_filter_filter_not S S P), filter_union_filter_not_eq]
  omega

macro "solve_boundary_count" S:term "," P:term "," h_unique:term "," mem_thm:term : tactic =>
  `(tactic| (
    apply card_filter_ge_sub_one ($S) ($P)
    rw [card_le_one_iff]
    intro p q hp hq
    have h_mem := ($mem_thm)
    simp only [mem_filter, not_lt, h_mem] at hp hq
    have hp_blk : p ∈ all_black := hp.1.1
    have hq_blk : q ∈ all_black := hq.1.1
    have hpxp : px p < n := p.1.isLt
    have hpyp : py p < n := p.2.isLt
    have hpxq : px q < n := q.1.isLt
    have hpyq : py q < n := q.2.isLt
    apply ($h_unique) p hp_blk q hq_blk
    omega
  ))

theorem targetsWin_inequality
    (h_unique_y : ∀ p ∈ all_black, ∀ q ∈ all_black, py p = py q → p = q) :
    (targetsWin u v all_black).card ≥ (targetsW u v all_black).card - 1 := by
  solve_boundary_count (targetsW u v all_black),
  (fun p => 0 < py p), h_unique_y, mem_targetsW (n := n)

theorem targetsNin_inequality
    (h_unique_x : ∀ p ∈ all_black, ∀ q ∈ all_black, px p = px q → p = q) :
    (targetsNin u v all_black).card ≥ (targetsN u v all_black).card - 1 := by
  solve_boundary_count (targetsN u v all_black),
   (fun p => 0 < px p), h_unique_x, mem_targetsN (n := n)

theorem targetsSin_inequality
    (h_unique_x : ∀ p ∈ all_black, ∀ q ∈ all_black, px p = px q → p = q) :
    (targetsSin u v all_black).card ≥ (targetsS u v all_black).card - 1 := by
  solve_boundary_count (targetsS u v all_black),
  (fun p => px p < n - 1), h_unique_x, mem_targetsS (n := n)

theorem targetsEin_inequality
    (h_unique_y : ∀ p ∈ all_black, ∀ q ∈ all_black, py p = py q → p = q) :
    (targetsEin u v all_black).card ≥ (targetsE u v all_black).card - 1 := by
  solve_boundary_count (targetsE u v all_black),
  (fun p => py p < n - 1), h_unique_y, mem_targetsE (n := n)

end MainRegions

section IncidenceCount

variable {u v all_black : Finset (Point n)}

def incidence_count (u v all_black : Finset (Point n)) (p : Point n) : ℕ :=
  (if p ∈ targetsW u v all_black then 1 else 0) +
  (if p ∈ targetsN u v all_black then 1 else 0) +
  (if p ∈ targetsE u v all_black then 1 else 0) +
  (if p ∈ targetsS u v all_black then 1 else 0)

lemma sum_card_eq_sum_incidence :
    (targetsW u v all_black).card + (targetsN u v all_black).card +
    (targetsE u v all_black).card + (targetsS u v all_black).card
    = ∑ p ∈  all_black, incidence_count u v all_black p := by
  simp only [incidence_count]
  rw [sum_add_distrib, sum_add_distrib, sum_add_distrib]
  congr 1; congr 1; congr 1
  all_goals {
    rw [card_eq_sum_ones]; rw [← sum_filter]
    apply sum_congr
    · ext x; simp only [mem_filter]; simp  [targetsW, targetsN, targetsE, targetsS]
    · intro x hx; rfl
  }

lemma u_parts_intersection_eq_u
    (h_u_mono : ∀ a ∈ u, ∀ b ∈ u, px a < px b → py a < py b)
    (h_u_inj : ∀ a ∈ u, ∀ b ∈ u, px a = px b → a = b)
    : u_lower u ∩ u_upper u = u := by
  ext p; simp
  constructor
  · intro ⟨⟨qx, qy, hq_u, hq_bx, hq_by⟩, ⟨rx, ry, hr_u, hr_bx, hr_by⟩⟩
    let q : Point n := (qx, qy); let r : Point n := (rx, ry)
    have hq_mem : q ∈ u := hq_u; have hr_mem : r ∈ u := hr_u
    rcases lt_trichotomy (px q) (px r) with h_lt | h_eq | h_gt
    · have := h_u_mono q hq_mem r hr_mem h_lt
      solve_grid
    · have h_same : q = r := h_u_inj q hq_mem r hr_mem h_eq
      rw [Prod.ext_iff] at h_same; obtain ⟨rfl, rfl⟩ := h_same
      convert hq_mem
      ext <;> solve_grid
    · solve_grid
  · intro hp
    constructor <;> { use p.1, p.2, hp}

lemma v_parts_intersection_eq_v
    (h_v_mono : ∀ a ∈ v, ∀ b ∈ v, px a < px b → py b < py a)
    (h_v_inj : ∀ a ∈ v, ∀ b ∈ v, px a = px b → a = b)
    : v_lower v ∩ v_upper v = v := by
  ext p; simp
  constructor
  · intro ⟨⟨qx, qy, hq_v, hq_bx, hq_by⟩, ⟨rx, ry, hr_v, hr_bx, hr_by⟩⟩
    let q : Point n := (qx, qy); let r : Point n := (rx, ry)
    have hq_mem : q ∈ v := hq_v; have hr_mem : r ∈ v := hr_v
    rcases lt_trichotomy (px r) (px q) with h_lt | h_eq | h_gt
    · have := h_v_mono r hr_mem q hq_mem h_lt
      solve_grid
    · have h_same : r = q := h_v_inj r hr_mem q hq_mem h_eq
      rw [Prod.ext_iff] at h_same; obtain ⟨rfl, rfl⟩ := h_same
      convert hq_mem
      ext <;> solve_grid
    · solve_grid
  · intro hp
    constructor <;> { use p.1, p.2, hp}

lemma inter_card_le_one
    (h_u_mono : ∀ a ∈ u, ∀ b ∈ u, px a < px b → py a < py b)
    (h_v_mono : ∀ a ∈ v, ∀ b ∈ v, px a < px b → py b < py a)
    (h_u_inj : ∀ a ∈ u, ∀ b ∈ u, px a = px b → a = b)
    : (u ∩ v).card ≤ 1 := by
  by_contra h_gt_one
  rw [not_le, one_lt_card_iff] at h_gt_one
  obtain ⟨p, q, hp, hq, h_ne⟩ := h_gt_one
  rw [mem_inter] at hp hq
  rcases lt_trichotomy (px p) (px q) with h_lt | h_eq | h_gt
  · have h_u_inc : py p < py q := h_u_mono p hp.1 q hq.1 h_lt
    have h_v_dec : py q < py p := h_v_mono p hp.2 q hq.2 h_lt
    linarith
  · have h_same : p = q := h_u_inj p hp.1 q hq.1 h_eq
    contradiction
  · have h_u_inc : py q < py p := h_u_mono q hq.1 p hp.1 h_gt
    have h_v_dec : py p < py q := h_v_mono q hq.2 p hp.2 h_gt
    linarith

lemma incidence_of_u_diff
    (pivot : Point n) (h_inter : u ∩ v = {pivot})
    (h_u_mono : ∀ a ∈ u, ∀ b ∈ u, px a < px b → py a < py b)
    : ∀ p ∈ u \ {pivot},
      (px p < px pivot → p ∈ regionWExtend u v) ∧
      (px pivot < px p → p ∈ regionEExtend u v) := by
  have h_piv_u : pivot ∈ u := mem_of_mem_inter_left (by rw [h_inter]; simp)
  have h_piv_v : pivot ∈ v := mem_of_mem_inter_right (by rw [h_inter]; simp)
  intro p hp
  rw [mem_sdiff, mem_singleton] at hp
  obtain ⟨hp_u, h_ne_piv⟩ := hp
  constructor
  · intro h_lt
    have hy_lt : py p < py pivot := h_u_mono p hp_u pivot h_piv_u h_lt
    simp only at h_lt hy_lt
    simp
    constructor
    · use p.1, p.2
    · use pivot.1, pivot.2
      simp only [Fin.le_iff_val_le_val]
      constructor
      · exact h_piv_v
      · constructor <;> linarith
  · intro h_gt
    have hy_gt : py pivot < py p := h_u_mono pivot h_piv_u p hp_u h_gt
    simp only at h_gt hy_gt
    simp
    constructor
    · use p.1, p.2
    · use pivot.1, pivot.2
      simp only [Fin.le_iff_val_le_val]
      constructor
      · exact h_piv_v
      · constructor <;> linarith

lemma incidence_of_v_diff
    (pivot : Point n)
    (h_inter : u ∩ v = {pivot})
    (h_v_mono : ∀ a ∈ v, ∀ b ∈ v, px a < px b → py b < py a)
    : ∀ p ∈ v \ {pivot},
      (px p < px pivot → p ∈ regionNExtend u v) ∧
      (px pivot < px p → p ∈ regionSExtend u v) := by
  have h_piv_u : pivot ∈ u := mem_of_mem_inter_left (by rw [h_inter]; simp)
  have h_piv_v : pivot ∈ v := mem_of_mem_inter_right (by rw [h_inter]; simp)
  intro p hp
  rw [mem_sdiff, mem_singleton] at hp
  obtain ⟨hp_v, h_ne_piv⟩ := hp
  constructor
  · intro h_lt
    have hy_gt : py pivot < py p := h_v_mono p hp_v pivot h_piv_v h_lt
    simp only at h_lt hy_gt
    simp
    constructor
    · use pivot.1, pivot.2
      simp only [Fin.le_iff_val_le_val]
      constructor
      · exact h_piv_u
      · constructor <;> linarith
    · use p.1, p.2
  · intro h_gt
    have hy_lt : py p < py pivot := h_v_mono pivot h_piv_v p hp_v h_gt
    simp only at h_gt hy_lt
    simp
    constructor
    · use pivot.1, pivot.2
      simp only [Fin.le_iff_val_le_val]
      constructor
      · exact h_piv_u
      · constructor <;> linarith
    · use p.1, p.2

lemma pivot_in_all_regions
    (pivot : Point n)
    (h_piv_u : pivot ∈ u)
    (h_piv_v : pivot ∈ v)
    : pivot ∈ regionWExtend u v ∧ pivot ∈ regionEExtend u v ∧
      pivot ∈ regionNExtend u v ∧ pivot ∈ regionSExtend u v := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · simp;  constructor <;> use pivot.1, pivot.2

lemma incidence_of_intersection
    (pivot : Point n) (h_piv_u : pivot ∈ u) (h_piv_v : pivot ∈ v)
    (h_u_mono : ∀ a ∈ u, ∀ b ∈ u, px a < px b → py a < py b)
    (h_v_mono : ∀ a ∈ v, ∀ b ∈ v, px a < px b → py b < py a)
    (h_u_inj : ∀ a ∈ u, ∀ b ∈ u, px a = px b → a = b)
    : u ∩ v = {pivot} := by
  ext p
  simp
  constructor
  · intro ⟨hp_u, hp_v⟩
    rcases lt_trichotomy (px p) (px pivot) with h_lt | h_eq | h_gt
    · have h_u_lt : py p < py pivot := h_u_mono p hp_u pivot h_piv_u h_lt
      have h_v_gt : py pivot < py p := h_v_mono p hp_v pivot h_piv_v h_lt
      simp only at h_u_lt h_v_gt
      linarith
    · exact h_u_inj p hp_u pivot h_piv_u h_eq
    · have h_u_gt : py pivot < py p := h_u_mono pivot h_piv_u p hp_u h_gt
      have h_v_lt : py p < py pivot := h_v_mono pivot h_piv_v p hp_v h_gt
      simp only  at h_u_gt h_v_lt
      linarith
  · intro h_eq
    subst h_eq
    exact ⟨h_piv_u, h_piv_v⟩

lemma incidence_count_of_pivot
    (pivot : Point n)
    (h_inter : u ∩ v = {pivot})
    (h_piv_in_all : pivot ∈ all_black)
    : incidence_count u v all_black pivot = 4 := by
  have h_piv_u : pivot ∈ u := mem_of_mem_inter_left (by rw [h_inter]; simp)
  have h_piv_v : pivot ∈ v := mem_of_mem_inter_right (by rw [h_inter]; simp)
  have h_u_lo : pivot ∈ u_lower u := by rw [mem_u_lower]; use pivot
  have h_u_up : pivot ∈ u_upper u := by rw [mem_u_upper]; use pivot
  have h_v_lo : pivot ∈ v_lower v := by rw [mem_v_lower]; use pivot
  have h_v_up : pivot ∈ v_upper v := by rw [mem_v_upper]; use pivot
  have hW : pivot ∈ regionWExtend u v := by rw [mem_regionWExtend]; exact ⟨h_u_lo, h_v_lo⟩
  have hN : pivot ∈ regionNExtend u v := by rw [mem_regionNExtend]; exact ⟨h_u_up, h_v_lo⟩
  have hE : pivot ∈ regionEExtend u v := by rw [mem_regionEExtend]; exact ⟨h_u_up, h_v_up⟩
  have hS : pivot ∈ regionSExtend u v := by rw [mem_regionSExtend]; exact ⟨h_u_lo, h_v_up⟩
  unfold incidence_count
  simp only [mem_targetsW, mem_targetsN, mem_targetsS, mem_targetsE]
  simp only [h_piv_in_all, hW, hN, hE, hS]
  rfl

lemma incidence_count_of_u_diff
    (p : Point n) (hp : p ∈ u) (hp_not_v : p ∉ v)
    (pivot : Point n) (h_inter : u ∩ v = {pivot})
    (hu_sub : u ⊆ all_black)
    (h_u_mono : ∀ a ∈ u, ∀ b ∈ u, px a < px b → py a < py b)
    (h_v_mono : ∀ a ∈ v, ∀ b ∈ v, px a < px b → py b < py a)
    (h_u_inj : ∀ a ∈ u, ∀ b ∈ u, px a = px b → a = b)
    (h_v_inj : ∀ a ∈ v, ∀ b ∈ v, px a = px b → a = b)
    : incidence_count u v all_black p = 2 := by

  have hp_all : p ∈ all_black := hu_sub hp
  have h_piv_v : pivot ∈ v := mem_of_mem_inter_right (by rw [h_inter]; simp)
  have h_piv_u : pivot ∈ u := mem_of_mem_inter_left (by rw [h_inter]; simp)
  have h_u_lo : p ∈ u_lower u := by
    rw [mem_u_lower]; exact ⟨p, hp, le_refl (px p), le_refl (py p)⟩
  have h_u_up : p ∈ u_upper u := by
    rw [mem_u_upper]; exact ⟨p, hp, le_refl (px p), le_refl (py p)⟩
  have h_in_W : p ∈ regionWExtend u v ↔ p ∈ v_lower v := by
    rw [regionWExtend, mem_inter, and_iff_right h_u_lo]
  have h_in_N : p ∈ regionNExtend u v ↔ p ∈ v_lower v := by
    rw [regionNExtend, mem_inter, and_iff_right h_u_up]
  have h_in_E : p ∈ regionEExtend u v ↔ p ∈ v_upper v := by
    rw [regionEExtend, mem_inter, and_iff_right h_u_up]
  have h_in_S : p ∈ regionSExtend u v ↔ p ∈ v_upper v := by
    rw [regionSExtend, mem_inter, and_iff_right h_u_lo]
  have h_not_both : ¬(p ∈ v_lower v ∧ p ∈ v_upper v) := by
    intro h_both
    have h_in_v : p ∈ v := by
      rw [← v_parts_intersection_eq_v h_v_mono h_v_inj, mem_inter]
      exact h_both
    contradiction
  unfold incidence_count
  rcases lt_trichotomy (px p) (px pivot) with h_lt | h_eq | h_gt
  · have h_lo : p ∈ v_lower v := by
      have hy : py p < py pivot := h_u_mono p hp pivot h_piv_u h_lt
      rw [mem_v_lower]; use pivot; exact ⟨h_piv_v, le_of_lt h_lt, le_of_lt hy⟩
    have h_not_up : p ∉ v_upper v := fun h_up => h_not_both ⟨h_lo, h_up⟩
    simp [h_in_W, h_in_N, h_in_E, h_in_S, h_lo, h_not_up, hp_all]
  · have h_p_eq_pivot: p = pivot := by
      refine h_u_inj p hp pivot h_piv_u h_eq
    subst h_p_eq_pivot
    contradiction
  · have h_up : p ∈ v_upper v := by
      have hy : py pivot < py p := h_u_mono pivot h_piv_u p hp h_gt
      rw [mem_v_upper]; use pivot; exact ⟨h_piv_v, le_of_lt h_gt, le_of_lt hy⟩
    have h_not_lo : p ∉ v_lower v := fun h_lo => h_not_both ⟨h_lo, h_up⟩
    simp [h_in_W, h_in_N, h_in_E, h_in_S, h_up, h_not_lo, hp_all]

lemma incidence_count_of_v_diff
    (p : Point n) (hp : p ∈ v) (hp_not_u : p ∉ u)
    (pivot : Point n) (h_inter : u ∩ v = {pivot})
    (hv_sub : v ⊆ all_black)
    (h_u_mono : ∀ a ∈ u, ∀ b ∈ u, px a < px b → py a < py b)
    (h_v_mono : ∀ a ∈ v, ∀ b ∈ v, px a < px b → py b < py a)
    (h_u_inj : ∀ a ∈ u, ∀ b ∈ u, px a = px b → a = b)
    (h_v_inj : ∀ a ∈ v, ∀ b ∈ v, px a = px b → a = b)
    : incidence_count u v all_black p = 2 := by
  have hp_all : p ∈ all_black := hv_sub hp
  have h_piv_v : pivot ∈ v := mem_of_mem_inter_right (by rw [h_inter]; simp)
  have h_piv_u : pivot ∈ u := mem_of_mem_inter_left (by rw [h_inter]; simp)
  have h_v_lo : p ∈ v_lower v := by
    rw [mem_v_lower]; exact ⟨p, hp, le_refl (px p), le_refl (py p)⟩
  have h_v_up : p ∈ v_upper v := by
    rw [mem_v_upper]; exact ⟨p, hp, le_refl (px p), le_refl (py p)⟩
  have h_in_W : p ∈ regionWExtend u v ↔ p ∈ u_lower u := by
    rw [regionWExtend, mem_inter, and_iff_left h_v_lo]
  have h_in_N : p ∈ regionNExtend u v ↔ p ∈ u_upper u := by
    rw [regionNExtend, mem_inter, and_iff_left h_v_lo];
  have h_in_E : p ∈ regionEExtend u v ↔ p ∈ u_upper u := by
    rw [regionEExtend, mem_inter, and_iff_left h_v_up]
  have h_in_S : p ∈ regionSExtend u v ↔ p ∈ u_lower u := by
    rw [regionSExtend, mem_inter, and_iff_left h_v_up]
  have h_not_both : ¬(p ∈ u_lower u ∧ p ∈ u_upper u) := by
    intro h_both
    have h_in_u : p ∈ u := by
      rw [← u_parts_intersection_eq_u h_u_mono h_u_inj, mem_inter]
      exact h_both
    contradiction
  unfold incidence_count
  rcases lt_trichotomy (px p) (px pivot) with h_lt | h_eq | h_gt
  · have h_up : p ∈ u_upper u := by
      have hy : py pivot < py p := h_v_mono p hp pivot h_piv_v h_lt
      rw [mem_u_upper]; use pivot; exact ⟨h_piv_u, le_of_lt h_lt, le_of_lt hy⟩
    have h_not_lo : p ∉ u_lower u := fun h_lo => h_not_both ⟨h_lo, h_up⟩
    simp [h_in_W, h_in_N, h_in_E, h_in_S, h_up, h_not_lo, hp_all]
  · have h_p_eq_pivot: p = pivot := by
      refine h_v_inj p hp pivot h_piv_v h_eq
    subst h_p_eq_pivot
    contradiction
  · have h_lo : p ∈ u_lower u := by
      have hy : py p < py pivot := h_v_mono pivot h_piv_v p hp h_gt
      rw [mem_u_lower]; use pivot; exact ⟨h_piv_u, le_of_lt h_gt, le_of_lt hy⟩
    have h_not_lo : p ∉ u_upper u := fun h_up => h_not_both ⟨h_lo, h_up⟩
    simp [h_in_W, h_in_N, h_in_E, h_in_S, h_lo, h_not_lo, hp_all]

lemma covering_of_maximal_u
    (p : Point n) (hp : p ∈ all_black) (hp_not_u : p ∉ u)
    (h_maximal : ∀ p ∈ all_black, p ∉ u →
        (∀ q ∈ u, px q < px p → py q < py p) →
        (∀ q ∈ u, px p < px q → py p < py q) →
        False)
    : p ∈ u_lower u ∨ p ∈ u_upper u := by
  by_contra h_not_covered
  push_neg at h_not_covered
  obtain ⟨h_not_lo, h_not_up⟩ := h_not_covered
  simp only [mem_u_lower, not_exists, not_and] at h_not_lo
  simp only [mem_u_upper, not_exists, not_and] at h_not_up
  apply h_maximal p hp hp_not_u
  · intro q hq hx_lt
    specialize h_not_lo q hq
    have h_x_le : px q ≤ px p := le_of_lt hx_lt
    have h_not_y_le : ¬(py p ≤ py q) := fun h => h_not_lo h_x_le h
    linarith
  · intro q hq hx_lt
    specialize h_not_up q hq
    have h_x_le : px p ≤ px q := le_of_lt hx_lt
    have h_not_y_le : ¬(py q ≤ py p) := fun h => h_not_up h_x_le h
    linarith

lemma covering_of_maximal_v
    (p : Point n) (hp : p ∈ all_black) (hp_not_v : p ∉ v)
    (h_maximal : ∀ p ∈ all_black, p ∉ v →
        (∀ q ∈ v, px q < px p → py p < py q) →
        (∀ q ∈ v, px p < px q → py q < py p) →
        False)
    : p ∈ v_lower v ∨ p ∈ v_upper v := by
  by_contra h_not_covered
  push_neg at h_not_covered
  obtain ⟨h_not_lo, h_not_up⟩ := h_not_covered
  simp only [mem_v_lower, not_exists, not_and] at h_not_lo
  simp only [mem_v_upper, not_exists, not_and] at h_not_up
  apply h_maximal p hp hp_not_v
  · intro q hq hx_lt
    specialize h_not_up q hq
    have h_x_le : px q ≤ px p := le_of_lt hx_lt
    have h_not_y_le : ¬(py q ≤ py p) := fun h => h_not_up h_x_le h
    linarith
  · intro q hq hx_lt
    specialize h_not_lo q hq
    have h_x_le : px p ≤ px q := le_of_lt hx_lt
    have h_not_y_le : ¬(py p ≤ py q) := fun h => h_not_lo h_x_le h
    linarith

lemma incidence_count_of_others
    (p : Point n) (hp : p ∈ all_black) (hp_not_u : p ∉ u) (hp_not_v : p ∉ v)
    (h_u_mono : ∀ a ∈ u, ∀ b ∈ u, px a < px b → py a < py b)
    (h_v_mono : ∀ a ∈ v, ∀ b ∈ v, px a < px b → py b < py a)
    (h_u_inj : ∀ a ∈ u, ∀ b ∈ u, px a = px b → a = b)
    (h_v_inj : ∀ a ∈ v, ∀ b ∈ v, px a = px b → a = b)
    (h_u_max : ∀ p ∈ all_black, p ∉ u →
        (∀ q ∈ u, px q < px p → py q < py p) →
        (∀ q ∈ u, px p < px q → py p < py q) → False)
    (h_v_max : ∀ p ∈ all_black, p ∉ v →
        (∀ q ∈ v, px q < px p → py p < py q) →
        (∀ q ∈ v, px p < px q → py q < py p) → False)
    : incidence_count u v all_black p = 1 := by
  have h_u_cover : p ∈ u_lower u ∨ p ∈ u_upper u :=
    covering_of_maximal_u p hp hp_not_u h_u_max
  have h_u_exclusive : ¬(p ∈ u_lower u ∧ p ∈ u_upper u) := by
    intro h_both
    have : p ∈ u := by
      rw [← u_parts_intersection_eq_u h_u_mono h_u_inj, mem_inter]; exact h_both
    contradiction
  have h_u_exact : (p ∈ u_lower u) ≠ (p ∈ u_upper u) := by
    rcases h_u_cover with h_lo | h_up
    · simp only [h_lo]; intro h_up
      rw [← h_up] at h_u_exclusive; exact h_u_exclusive ⟨h_lo, trivial⟩
    · simp only [h_up]; intro h_lo;
      rw [h_lo] at h_u_exclusive; exact h_u_exclusive ⟨trivial, h_up⟩
  have h_v_cover : p ∈ v_lower v ∨ p ∈ v_upper v :=
    covering_of_maximal_v p hp hp_not_v h_v_max
  have h_v_exclusive : ¬(p ∈ v_lower v ∧ p ∈ v_upper v) := by
    intro h_both
    have : p ∈ v := by
      rw [← v_parts_intersection_eq_v h_v_mono h_v_inj, mem_inter]; exact h_both
    contradiction
  have h_v_exact : (p ∈ v_lower v) ≠ (p ∈ v_upper v) := by
    rcases h_v_cover with h_lo | h_up
    · simp only [h_lo]; intro h_up
      rw [← h_up] at h_v_exclusive; exact h_v_exclusive ⟨h_lo ,trivial⟩
    · simp only[h_up]; intro h_lo
      rw [h_lo] at h_v_exclusive; exact h_v_exclusive ⟨trivial, h_up⟩
  have hW : p ∈ regionWExtend u v ↔ (p ∈ u_lower u ∧ p ∈ v_lower v) := by
    rw [regionWExtend, mem_inter]
  have hN : p ∈ regionNExtend u v ↔ (p ∈ u_upper u ∧ p ∈ v_lower v) := by
    rw [regionNExtend, mem_inter]
  have hE : p ∈ regionEExtend u v ↔ (p ∈ u_upper u ∧ p ∈ v_upper v) := by
    rw [regionEExtend, mem_inter]
  have hS : p ∈ regionSExtend u v ↔ (p ∈ u_lower u ∧ p ∈ v_upper v) := by
    rw [regionSExtend, mem_inter]
  unfold incidence_count
  simp only [mem_targetsW, mem_targetsN, mem_targetsS, mem_targetsE, hp]
  simp only [hW, hN, hE, hS]
  by_cases hu_lo : p ∈ u_lower u <;> by_cases hv_lo : p ∈ v_lower v
  · have hu_up : p ∉ u_upper u := by
      simp only [hu_lo] at h_u_exact; exact fun h_in => h_u_exact (eq_true h_in).symm
    have hv_up : p ∉ v_upper v := by
      simp only [hv_lo] at h_v_exact; exact fun h_in => h_v_exact (eq_true h_in).symm
    simp [hu_lo, hv_lo, hu_up, hv_up]
  · have hu_up : p ∉ u_upper u := by
      simp only [hu_lo] at h_u_exact; exact fun h_in => h_u_exact (eq_true h_in).symm
    have hv_up : p ∈ v_upper v := by
      simp only[hv_lo] at h_v_exact
      by_contra h_not_in; rw [eq_false h_not_in] at h_v_exact; contradiction
    simp [hu_lo, hv_lo, hu_up, hv_up]
  · have hu_up : p ∈ u_upper u := by
      simp only [hu_lo] at h_u_exact
      by_contra h_not_in; rw [eq_false h_not_in] at h_u_exact; contradiction
    have hv_up : p ∉ v_upper v := by
      simp only [hv_lo] at h_v_exact; exact fun h_in => h_v_exact (eq_true h_in).symm
    simp [hu_lo, hv_lo, hu_up, hv_up]
  · have hu_up : p ∈ u_upper u := by
      simp only [hu_lo] at h_u_exact
      by_contra h_not_in; rw [eq_false h_not_in] at h_u_exact; contradiction
    have hv_up : p ∈ v_upper v := by
      simp only [hv_lo] at h_v_exact;
      by_contra h_not_in; rw [eq_false h_not_in] at h_v_exact; contradiction
    simp [hu_lo, hv_lo, hu_up, hv_up]

end IncidenceCount

section LabelingConsistency

variable {n : ℕ} {all_black : Finset (Point n)}

@[simp] lemma px_mk_val (x y : Fin n) : px (x, y) = x.val := rfl
@[simp] lemma py_mk_val (x y : Fin n) : py (x, y) = y.val := rfl

variable {n : ℕ} [NeZero n] {all_black : Finset (Point n)}

lemma fin_val_sub_one_eq {i : Fin n} (h : 0 < i.val) :
    (i - 1).val = i.val - 1 := by
  apply Fin.val_sub_one_of_ne_zero; exact ne_of_gt h

lemma fin_val_add_one_eq {i : Fin n} (h : i.val < n - 1) :
    (i + 1).val = i.val + 1 := by
  rw [Fin.val_add]; simp; rw [Nat.mod_eq_of_lt]; omega

macro "my_solver" : tactic => `(tactic| first | omega | linarith)
macro "solve_matilda_mem" : tactic => `(tactic| {
  simp only [Matilda.mem]
  repeat constructor <;> repeat my_solver
})

variable {n : ℕ} [NeZero n]
variable {all_black : Finset (Point n)}
variable (m : Matilda n all_black)
variable (u v : Finset (Point n))
variable (h_u_mono : ∀ a ∈ u, ∀ b ∈ u, px a ≤ px b → py a ≤ py b)
variable (h_v_mono : ∀ a ∈ v, ∀ b ∈ v, px a ≤ px b → py b ≤ py a)
variable (h_u_inj : ∀ a ∈ u, ∀ b ∈ u, py a = py b → a = b)
variable (h_v_inj : ∀ p ∈ v, ∀ q ∈ v, px p = px q → p = q)
variable (h_unique_x : ∀ p ∈ all_black, ∀ q ∈ all_black, px p = px q → p = q)
variable (h_unique_y : ∀ p ∈ all_black, ∀ q ∈ all_black, py p = py q → p = q)

lemma unique_label_W (m : Matilda n all_black) (p q : Point n)
    (hp : p ∈ all_black) (hq : q ∈ all_black) (h_ne : p ≠ q)
    (hp_pos : 0 < py p) (hq_pos : 0 < py q)
    (hp_in : m.mem ⟨p.1, p.2 - 1⟩)
    (hq_in : m.mem ⟨q.1, q.2 - 1⟩)
    (h_unique_y : ∀ p ∈ all_black, ∀ q ∈ all_black, py p = py q → p = q) : False := by
  simp only [Matilda.mem, px_mk_val, py_mk_val] at hp_in hq_in
  have h_p_sub : ↑(p.2 - 1) = py p - 1 := fin_val_sub_one_eq hp_pos
  have h_q_sub : ↑(q.2 - 1) = py q - 1 := fin_val_sub_one_eq hq_pos
  rcases lt_trichotomy (py p) (py q) with h_lt | h_eq | h_gt
  · have h_p_in_m : m.mem p := by solve_matilda_mem
    exact m.h_disjoint p hp h_p_in_m
  · exact h_ne (h_unique_y p hp q hq h_eq)
  · have h_q_in_m : m.mem q := by solve_matilda_mem
    exact m.h_disjoint q hq h_q_in_m

lemma unique_label_N (m : Matilda n all_black) (p q : Point n)
    (hp : p ∈ all_black) (hq : q ∈ all_black) (h_ne : p ≠ q)
    (hp_pos : 0 < px p) (hq_pos : 0 < px q)
    (hp_in : m.mem ⟨p.1 - 1, p.2⟩)
    (hq_in : m.mem ⟨q.1 - 1, q.2⟩)
    (h_unique_x : ∀ p ∈ all_black, ∀ q ∈ all_black, px p = px q → p = q) : False := by
  simp only [Matilda.mem, px_mk_val, py_mk_val] at hp_in hq_in
  have h_p_sub : ↑(p.1 - 1) = px p - 1 := fin_val_sub_one_eq hp_pos
  have h_q_sub : ↑(q.1 - 1) = px q - 1 := fin_val_sub_one_eq hq_pos
  rcases lt_trichotomy (px p) (px q) with h_lt | h_eq | h_gt
  · have h_p_in_m : m.mem p := by solve_matilda_mem
    exact m.h_disjoint p hp h_p_in_m
  · exact h_ne (h_unique_x p hp q hq h_eq)
  · have h_q_in_m : m.mem q := by solve_matilda_mem
    exact m.h_disjoint q hq h_q_in_m

lemma unique_label_E (m : Matilda n all_black) (p q : Point n)
    (hp : p ∈ all_black) (hq : q ∈ all_black) (h_ne : p ≠ q)
    (hp_bound : py p < n - 1) (hq_bound : py q < n - 1)
    (hp_in : m.mem ⟨p.1, p.2 + 1⟩)
    (hq_in : m.mem ⟨q.1, q.2 + 1⟩)
    (h_unique_y : ∀ p ∈ all_black, ∀ q ∈ all_black, py p = py q → p = q) : False := by
  simp only [Matilda.mem, px_mk_val, py_mk_val] at hp_in hq_in
  have h_p_add : ↑(p.2 + 1) = py p + 1 := fin_val_add_one_eq hp_bound
  have h_q_add : ↑(q.2 + 1) = py q + 1 := fin_val_add_one_eq hq_bound
  rw [h_p_add] at hp_in; rw [h_q_add] at hq_in
  rcases lt_trichotomy (py p) (py q) with h_lt | h_eq | h_gt
  · have h_q_in_m : m.mem q := by solve_matilda_mem
    exact m.h_disjoint q hq h_q_in_m
  · exact h_ne (h_unique_y p hp q hq h_eq)
  · have h_p_in_m : m.mem p := by solve_matilda_mem
    exact m.h_disjoint p hp h_p_in_m

lemma unique_label_S (m : Matilda n all_black) (p q : Point n)
    (hp : p ∈ all_black) (hq : q ∈ all_black) (h_ne : p ≠ q)
    (hp_bound : px p < n - 1) (hq_bound : px q < n - 1)
    (hp_in : m.mem ⟨p.1 + 1, p.2⟩)
    (hq_in : m.mem ⟨q.1 + 1, q.2⟩)
    (h_unique_x : ∀ p ∈ all_black, ∀ q ∈ all_black, px p = px q → p = q) : False := by

  simp only [Matilda.mem, px_mk_val, py_mk_val] at hp_in hq_in
  have h_p_add : ↑(p.1 + 1) = px p + 1 := fin_val_add_one_eq hp_bound
  have h_q_add : ↑(q.1 + 1) = px q + 1 := fin_val_add_one_eq hq_bound
  rcases lt_trichotomy (px p) (px q) with h_lt | h_eq | h_gt
  · have h_q_in_m : m.mem q := by solve_matilda_mem
    exact m.h_disjoint q hq h_q_in_m
  · exact h_ne (h_unique_x p hp q hq h_eq)
  · have h_p_in_m : m.mem p := by solve_matilda_mem
    exact m.h_disjoint p hp h_p_in_m

lemma disjoint_label_W_N (m : Matilda n all_black) (bw bn : Point n)
    (hbw : bw ∈ all_black) (hbn : bn ∈ all_black)
    (hbw_pos : 0 < py bw) (hbn_pos : 0 < px bn)
    (h_u_mono : ∀ a ∈ u, ∀ b ∈ u, px a ≤ px b → py a ≤ py b)
    (h_u_inj : ∀ a ∈ u, ∀ b ∈ u, py a = py b → a = b)
    (h_w_in : m.mem ⟨bw.1, bw.2 - 1⟩)
    (h_n_in : m.mem ⟨bn.1 - 1, bn.2⟩)
    (h_bw_reg : bw ∈ u_lower u)
    (h_bn_reg : bn ∈ u_upper u)
    : False := by
  simp only [Matilda.mem, px_mk_val, py_mk_val] at h_w_in h_n_in
  have h_w_sub : ↑(bw.2 - 1).val = py bw - 1 := fin_val_sub_one_eq hbw_pos
  have h_n_sub : ↑(bn.1 - 1).val = px bn - 1 := fin_val_sub_one_eq hbn_pos
  rcases (mem_u_lower u bw).mp h_bw_reg with ⟨u1, hu1_mem, hu1_x, hu1_y⟩
  rcases (mem_u_upper u bn).mp h_bn_reg with ⟨u2, hu2_mem, hu2_x, hu2_y⟩
  by_cases h_cross_x : px bn < px bw
  · have h_bn_in_m : m.mem bn := by solve_matilda_mem
    exact m.h_disjoint bn hbn h_bn_in_m
  by_cases h_cross_y : py bw < py bn
  · have h_bw_in_m : m.mem bw := by solve_matilda_mem
    exact m.h_disjoint bw hbw h_bw_in_m
  push_neg at h_cross_x h_cross_y
  have h_x_chain : px u1 ≤ px u2 := by linarith
  have h_y_chain : py u2 ≤ py u1 := by linarith
  have h_mono : py u1 ≤ py u2 := h_u_mono u1 hu1_mem u2 hu2_mem h_x_chain
  have h_y_eq : py u1 = py u2 := by linarith
  have h_u_eq : u1 = u2 := h_u_inj u1 hu1_mem u2 hu2_mem h_y_eq
  rw [h_u_eq] at hu1_x hu1_y
  have h_same_x : px bw = px bn := by linarith
  have h_same_y : py bw = py bn := by linarith
  have h_bw_in_m : m.mem bw := by
    simp only [Matilda.mem]
    repeat (first | constructor | linarith)
  exact m.h_disjoint bw hbw h_bw_in_m

lemma disjoint_label_E_S (m : Matilda n all_black) (be bs : Point n)
    (hbe : be ∈ all_black) (hbs : bs ∈ all_black)
    (hbe_bound : py be < n - 1) (hbs_bound : px bs < n - 1)
    (h_u_mono : ∀ a ∈ u, ∀ b ∈ u, px a ≤ px b → py a ≤ py b)
    (h_u_inj : ∀ a ∈ u, ∀ b ∈ u, py a = py b → a = b)
    (h_e_in : m.mem ⟨be.1, be.2 + 1⟩)
    (h_s_in : m.mem ⟨bs.1 + 1, bs.2⟩)
    (h_be_reg : be ∈ u_upper u)
    (h_bs_reg : bs ∈ u_lower u)
    : False := by
  simp only [Matilda.mem, px_mk_val, py_mk_val] at h_e_in h_s_in
  have h_e_add := fin_val_add_one_eq hbe_bound
  have h_s_add := fin_val_add_one_eq hbs_bound
  rcases (mem_u_upper u be).mp h_be_reg with ⟨u2, hu2_mem, hu2_x, hu2_y⟩
  rcases (mem_u_lower u bs).mp h_bs_reg with ⟨u1, hu1_mem, hu1_x, hu1_y⟩
  by_cases h_cross_x : px be < px bs
  · have h_bs_in_m : m.mem bs := by solve_matilda_mem
    exact m.h_disjoint bs hbs h_bs_in_m
  by_cases h_cross_y : py bs < py be
  · have h_be_in_m : m.mem be := by solve_matilda_mem
    exact m.h_disjoint be hbe h_be_in_m
  push_neg at h_cross_x h_cross_y
  have h_x_chain : px u1 ≤ px u2 := by linarith
  have h_y_chain : py u2 ≤ py u1 := by linarith
  have h_mono : py u1 ≤ py u2 := h_u_mono u1 hu1_mem u2 hu2_mem h_x_chain
  have h_y_eq : py u1 = py u2 := by linarith
  have h_u_eq : u1 = u2 := h_u_inj u1 hu1_mem u2 hu2_mem h_y_eq
  rw [h_u_eq] at hu1_x hu1_y
  have h_same_x : px be = px bs := by linarith
  have h_same_y : py be = py bs := by linarith
  have h_be_in_m : m.mem be := by
    simp only [Matilda.mem]
    repeat (first | constructor | linarith)
  exact m.h_disjoint be hbe h_be_in_m

lemma disjoint_label_E_N (m : Matilda n all_black) (be bn : Point n)
    (hbe : be ∈ all_black) (hbn : bn ∈ all_black)
    (hbe_bound : py be < n - 1) (hbn_pos : 0 < px bn)
    (h_v_mono : ∀ a ∈ v, ∀ b ∈ v, px a ≤ px b → py b ≤ py a)
    (h_v_inj : ∀ a ∈ v, ∀ b ∈ v, py a = py b → a = b)
    (h_e_in : m.mem ⟨be.1, be.2 + 1⟩)
    (h_n_in : m.mem ⟨bn.1 - 1, bn.2⟩)
    (h_be_reg : be ∈ v_upper v)
    (h_bn_reg : bn ∈ v_lower v)
    : False := by
  simp only [Matilda.mem, px_mk_val, py_mk_val] at h_e_in h_n_in
  have h_e_add : ↑(be.2 + 1).val = py be + 1 := fin_val_add_one_eq hbe_bound
  have h_n_sub : ↑(bn.1 - 1).val = px bn - 1 := fin_val_sub_one_eq hbn_pos
  rcases (mem_v_upper v be).mp h_be_reg with ⟨v1, hv1_mem, hv1_x, hv1_y⟩
  rcases (mem_v_lower v bn).mp h_bn_reg with ⟨v2, hv2_mem, hv2_x, hv2_y⟩
  by_cases h_cross_x : px bn < px be
  · have h_bn_in_m : m.mem bn := by solve_matilda_mem
    exact m.h_disjoint bn hbn h_bn_in_m
  by_cases h_cross_y : py bn < py be
  · have h_be_in_m : m.mem be := by solve_matilda_mem
    exact m.h_disjoint be hbe h_be_in_m
  push_neg at h_cross_x h_cross_y
  have h_x_chain : px v1 ≤ px v2 := by linarith
  have h_y_chain : py v1 ≤ py v2 := by linarith
  have h_mono : py v2 ≤ py v1 := h_v_mono v1 hv1_mem v2 hv2_mem h_x_chain
  have h_y_eq : py v1 = py v2 := by linarith
  have h_v_eq : v1 = v2 := h_v_inj v1 hv1_mem v2 hv2_mem h_y_eq
  rw [h_v_eq] at hv1_x hv1_y
  have h_same_x : px be = px bn := by linarith
  have h_same_y : py be = py bn := by linarith
  have h_be_in_m : m.mem be := by
    simp only [Matilda.mem]
    repeat (first | constructor | linarith)
  exact m.h_disjoint be hbe h_be_in_m

lemma disjoint_label_S_W (m : Matilda n all_black) (bs bw : Point n)
    (hbs : bs ∈ all_black) (hbw : bw ∈ all_black)
    (hbs_bound : px bs < n - 1) (hbw_pos : 0 < py bw)
    (h_v_mono : ∀ a ∈ v, ∀ b ∈ v, px a ≤ px b → py b ≤ py a)
    (h_v_inj : ∀ a ∈ v, ∀ b ∈ v, py a = py b → a = b)
    (h_s_in : m.mem ⟨bs.1 + 1, bs.2⟩)
    (h_w_in : m.mem ⟨bw.1, bw.2 - 1⟩)
    (h_bs_reg : bs ∈ v_upper v)
    (h_bw_reg : bw ∈ v_lower v)
    : False := by
  simp only [Matilda.mem, px_mk_val, py_mk_val] at h_s_in h_w_in
  have h_s_add : ↑(bs.1 + 1).val = px bs + 1 := fin_val_add_one_eq hbs_bound
  have h_w_sub : ↑(bw.2 - 1).val = py bw - 1 := fin_val_sub_one_eq hbw_pos
  rcases (mem_v_upper v bs).mp h_bs_reg with ⟨v2, hv2_mem, hv2_x, hv2_y⟩
  rcases (mem_v_lower v bw).mp h_bw_reg with ⟨v1, hv1_mem, hv1_x, hv1_y⟩
  by_cases h_cross_x : px bw < px bs
  · have h_bs_in_m : m.mem bs := by solve_matilda_mem
    exact m.h_disjoint bs hbs h_bs_in_m
  by_cases h_cross_y : py bw < py bs
  · have h_bw_in_m : m.mem bw := by solve_matilda_mem
    exact m.h_disjoint bw hbw h_bw_in_m
  push_neg at h_cross_x h_cross_y
  have h_x_chain : px v2 ≤ px v1 := by linarith
  have h_y_chain : py v2 ≤ py v1 := by linarith
  have h_mono : py v1 ≤ py v2 := h_v_mono v2 hv2_mem v1 hv1_mem h_x_chain
  have h_y_eq : py v2 = py v1 := by linarith
  have h_v_eq : v1 = v2 := h_v_inj v1 hv1_mem v2 hv2_mem h_y_eq.symm
  rw [h_v_eq] at hv1_x hv1_y
  have h_same_x : px bs = px bw := by linarith
  have h_same_y : py bs = py bw := by linarith
  have h_bs_in_m : m.mem bs := by
    simp only [Matilda.mem]
    repeat (first | constructor | linarith)
  exact m.h_disjoint bs hbs h_bs_in_m

lemma disjoint_label_W_E (m : Matilda n all_black) (bw be : Point n)
    (hbw : bw ∈ all_black)
    (hbw_pos : 0 < py bw) (hbe_bound : py be < n - 1)
    (h_u_mono : ∀ a ∈ u, ∀ b ∈ u, px a ≤ px b → py a ≤ py b)
    (h_v_mono : ∀ a ∈ v, ∀ b ∈ v, px a ≤ px b → py b ≤ py a)
    (h_u_inj : ∀ a ∈ u, ∀ b ∈ u, py a = py b → a = b)
    (h_w_in : m.mem ⟨bw.1, bw.2 - 1⟩)
    (h_e_in : m.mem ⟨be.1, be.2 + 1⟩)
    (h_bw_reg : bw ∈ regionWExtend u v)
    (h_be_reg : be ∈ regionEExtend u v)
    : False := by
  simp only [Matilda.mem, px_mk_val, py_mk_val] at h_w_in h_e_in
  have h_w_sub : ↑(bw.2 - 1).val = py bw - 1 := fin_val_sub_one_eq hbw_pos
  have h_e_add : ↑(be.2 + 1).val = py be + 1 := fin_val_add_one_eq hbe_bound
  obtain ⟨h_bw_u, h_bw_v⟩ := (mem_regionWExtend u v bw).mp h_bw_reg
  obtain ⟨h_be_u, h_be_v⟩ := (mem_regionEExtend u v be).mp h_be_reg
  rcases (mem_u_lower u bw).mp h_bw_u with ⟨u1, hu1_mem, hu1_x, hu1_y⟩
  rcases (mem_u_upper u be).mp h_be_u with ⟨u2, hu2_mem, hu2_x, hu2_y⟩
  rcases (mem_v_lower v bw).mp h_bw_v with ⟨v1, hv1_mem, hv1_x, hv1_y⟩
  rcases (mem_v_upper v be).mp h_be_v with ⟨v2, hv2_mem, hv2_x, hv2_y⟩
  by_cases h_lt : py bw < py be
  · have h_bw_in_m : m.mem bw := by solve_matilda_mem
    exact m.h_disjoint bw hbw h_bw_in_m
  push_neg at h_lt
  have h_y_chain_u : py u2 ≤ py u1 := by linarith
  have h_x_u_order : px u2 ≤ px u1 := by
    by_contra h_contra; push_neg at h_contra
    have h_mono := h_u_mono u1 hu1_mem u2 hu2_mem (le_of_lt h_contra)
    have h_y_eq : py u1 = py u2 := by linarith
    have h_u_eq : u1 = u2 := h_u_inj u1 hu1_mem u2 hu2_mem h_y_eq
    rw [h_u_eq] at h_contra; linarith
  have h_x_chain_all : px v2 ≤ px v1 := by linarith
  have h_y_v_order : py v1 ≤ py v2 := h_v_mono v2 hv2_mem v1 hv1_mem h_x_chain_all
  have h_y_final : py bw ≤ py be := by linarith
  have h_same_y : py bw = py be := by linarith
  have h_bw_in_m : m.mem bw := by
    simp only [Matilda.mem]
    repeat (first | constructor | linarith | omega)
  exact m.h_disjoint bw hbw h_bw_in_m

lemma disjoint_label_N_S (m : Matilda n all_black) (bn bs : Point n)
    (hbn : bn ∈ all_black)
    (hbn_pos : 0 < px bn) (hbs_bound : px bs < n - 1)
    (h_u_mono : ∀ a ∈ u, ∀ b ∈ u, px a ≤ px b → py a ≤ py b)
    (h_v_mono : ∀ a ∈ v, ∀ b ∈ v, px a ≤ px b → py b ≤ py a)
    (h_v_inj : ∀ a ∈ v, ∀ b ∈ v, py a = py b → a = b)
    (h_n_in : m.mem ⟨bn.1 - 1, bn.2⟩)
    (h_s_in : m.mem ⟨bs.1 + 1, bs.2⟩)
    (h_bn_reg : bn ∈ regionNExtend u v)
    (h_bs_reg : bs ∈ regionSExtend u v)
    : False := by

  simp only [Matilda.mem, px_mk_val, py_mk_val] at h_n_in h_s_in
  have h_n_sub : ↑(bn.1 - 1).val = px bn - 1 := fin_val_sub_one_eq hbn_pos
  have h_s_add : ↑(bs.1 + 1).val = px bs + 1 := fin_val_add_one_eq hbs_bound
  obtain ⟨h_bn_u, h_bn_v⟩ := (mem_regionNExtend u v bn).mp h_bn_reg
  obtain ⟨h_bs_u, h_bs_v⟩ := (mem_regionSExtend u v bs).mp h_bs_reg
  rcases (mem_u_upper u bn).mp h_bn_u with ⟨u1, hu1_mem, hu1_x, hu1_y⟩
  rcases (mem_u_lower u bs).mp h_bs_u with ⟨u2, hu2_mem, hu2_x, hu2_y⟩
  rcases (mem_v_lower v bn).mp h_bn_v with ⟨v1, hv1_mem, hv1_x, hv1_y⟩
  rcases (mem_v_upper v bs).mp h_bs_v with ⟨v2, hv2_mem, hv2_x, hv2_y⟩
  by_cases h_lt : px bn < px bs
  · have h_bn_in_m : m.mem bn := by solve_matilda_mem
    exact m.h_disjoint bn hbn h_bn_in_m
  push_neg at h_lt
  have h_x_chain_u : px u2 ≤ px u1 := by linarith
  have h_y_u_order : py u2 ≤ py u1 := h_u_mono u2 hu2_mem u1 hu1_mem h_x_chain_u
  have h_y_chain_all : py v2 ≤ py v1 := by linarith
  have h_x_v_order : px v1 ≤ px v2 := by
    by_contra h_contra; push_neg at h_contra
    have h_mono := h_v_mono v2 hv2_mem v1 hv1_mem (le_of_lt h_contra)
    have h_y_eq : py v1 = py v2 := by linarith
    have h_v_eq : v1 = v2 := h_v_inj v1 hv1_mem v2 hv2_mem h_y_eq
    rw [h_v_eq] at h_contra; linarith
  have h_x_final : px bn ≤ px bs := by linarith
  have h_same_x : px bn = px bs := by linarith
  have h_bn_in_m : m.mem bn := by
    simp only [Matilda.mem]
    repeat (first | constructor | linarith | omega)
  exact m.h_disjoint bn hbn h_bn_in_m

end LabelingConsistency

section LabelingMachinery

variable {n : ℕ} [NeZero n]

lemma matilda_eq_iff_bounds_eq (m1 m2 : Matilda n all_black) :
    m1 = m2 ↔
    m1.x_min = m2.x_min ∧ m1.x_max = m2.x_max ∧
    m1.y_min = m2.y_min ∧ m1.y_max = m2.y_max := by
  constructor
  · intro h; rw [h]; simp
  · intro h
    rcases m1 with ⟨x1, X1, y1, Y1, _, _, _, _⟩
    rcases m2 with ⟨x2, X2, y2, Y2, _, _, _, _⟩
    simp at h
    rcases h with ⟨rfl, rfl, rfl, rfl⟩
    congr

instance : Finite (Matilda n all_black) := by
  let f (m : Matilda n all_black) : (Fin n × Fin n × Fin n × Fin n) :=
    (
      ⟨m.x_min, lt_of_le_of_lt m.h_x_le m.h_x_bound⟩,
      ⟨m.x_max, m.h_x_bound⟩,
      ⟨m.y_min, lt_of_le_of_lt m.h_y_le m.h_y_bound⟩,
      ⟨m.y_max, m.h_y_bound⟩
    )
  apply Finite.of_injective f
  intro m1 m2 h
  simp [f] at h
  rw [matilda_eq_iff_bounds_eq]
  exact h

noncomputable instance : Fintype (Matilda n all_black) :=
  Fintype.ofFinite _

noncomputable def matildas (n : ℕ) [NeZero n] (all_black : Finset (Point n))
  : Finset (Matilda n all_black) := univ

inductive LabelType
  | W | N | E | S | X
  deriving DecidableEq, Repr, Fintype

structure Label (n : ℕ) where
  source : Point n
  type : LabelType
  deriving DecidableEq, Repr, Fintype

@[simp]
def Label.position (l : Label n) : Point n :=
  match l.type with
  | .W => ⟨l.source.1, l.source.2 -1⟩
  | .N => ⟨l.source.1 - 1, l.source.2⟩
  | .E => ⟨l.source.1, l.source.2 + 1⟩
  | .S => ⟨l.source.1 - 1, l.source.2⟩
  | .X => l.source

@[simp]
def label_pos (l : Label n) : Point n × Point n :=
  let p := l.source
  match l.type with
  | .W => (p, (p.1, p.2 - 1))
  | .N => (p, (p.1 - 1, p.2))
  | .E => (p, (p.1, p.2 + 1))
  | .S => (p, (p.1 + 1, p.2))
  | .X => (p, p)

@[simp]
def covers (m : Matilda n all_black) (l : Label n) : Prop :=
  m.mem (label_pos l).2

end LabelingMachinery

lemma am_gm_bound_nat (a b n : ℕ) (h_mul : n ≤ a * b) :
    (4 * n).sqrt ≤ a + b := by
  have h1 : 4 * n ≤ 4 * (a * b) := Nat.mul_le_mul_left 4 h_mul
  have h2 : 4 * (a * b) ≤ (a + b) * (a + b) := by
    calc
      4 * (a * b) = 2 * a * b + 2 * (a * b) := by ring
        _ ≤ (a ^ 2 + b ^ 2) + 2 * (a * b) := Nat.add_le_add_right (two_mul_le_add_sq a b) _
        _ = (a + b) * (a + b) := by ring
  calc
    (4 * n).sqrt
      ≤ (4 * (a * b)).sqrt       := Nat.sqrt_le_sqrt h1
    _ ≤ ((a + b) * (a + b)).sqrt := Nat.sqrt_le_sqrt h2
    _ = a + b                    := Nat.sqrt_eq (a + b)

structure IntersectionSetup (n : ℕ) [NeZero n] where

  u : Finset (Point n)
  v : Finset (Point n)
  all_black : Finset (Point n)
  pivot : Point n
  a : ℕ
  b : ℕ
  hu : u.card = a
  hv : v.card = b

  h_inter : u ∩ v = {pivot}
  hu_sub : u ⊆ all_black
  hv_sub : v ⊆ all_black
  h_n : all_black.card = n

  h_u_mono : ∀ p ∈ u, ∀ q ∈ u, px p < px q → py p < py q
  h_v_mono : ∀ p ∈ v, ∀ q ∈ v, px p < px q → py q < py p
  h_u_inj : ∀ p ∈ u, ∀ q ∈ u, px p = px q → p = q
  h_v_inj : ∀ p ∈ v, ∀ q ∈ v, px p = px q → p = q

  h_u_max : ∀ p ∈ all_black, p ∉ u →
      (∀ q ∈ u, px q < px p → py q < py p) →
      (∀ q ∈ u, px p < px q → py p < py q) → False
  h_v_max : ∀ p ∈ all_black, p ∉ v →
      (∀ q ∈ v, px q < px p → py p < py q) →
      (∀ q ∈ v, px p < px q → py q < py p) → False

  h_unique_x : ∀ p ∈ all_black, ∀ q ∈ all_black, px p = px q → p = q
  h_unique_y : ∀ p ∈ all_black, ∀ q ∈ all_black, py p = py q → p = q

namespace IntersectionSetup

variable {n : ℕ} [NeZero n] (c : IntersectionSetup n)

lemma u_mono_le : ∀ a ∈ c.u, ∀ b ∈ c.u, px a ≤ px b → py a ≤ py b :=
  chain_u_mono_le c.h_u_mono c.h_u_inj
lemma v_mono_le : ∀ a ∈ c.v, ∀ b ∈ c.v, px a ≤ px b → py b ≤ py a :=
  chain_v_mono_le c.h_v_mono c.h_v_inj
lemma u_inj_y : ∀ a ∈ c.u, ∀ b ∈ c.u, py a = py b → a = b :=
  chain_u_inj_y c.h_u_mono c.h_u_inj
lemma v_inj_y : ∀ a ∈ c.v, ∀ b ∈ c.v, py a = py b → a = b :=
  chain_v_inj_y c.h_v_mono c.h_v_inj

lemma pivot_mem_u : c.pivot ∈ c.u :=
  mem_of_mem_inter_left (by rw [c.h_inter]; simp)
lemma pivot_mem_v : c.pivot ∈ c.v :=
  mem_of_mem_inter_right (by rw [c.h_inter]; simp)
lemma union_sub : c.u ∪ c.v ⊆ c.all_black := union_subset c.hu_sub c.hv_sub

lemma a_pos : 1 ≤ c.a :=
  c.hu ▸ card_pos.mpr ⟨c.pivot, c.pivot_mem_u⟩
lemma b_pos : 1 ≤ c.b :=
  c.hv ▸ card_pos.mpr ⟨c.pivot, c.pivot_mem_v⟩

lemma disj_piv_u : Disjoint {c.pivot} (c.u \ {c.pivot}) := disjoint_sdiff_self_right
lemma disj_piv_v : Disjoint {c.pivot} (c.v \ {c.pivot}) := disjoint_sdiff_self_right
lemma disj_u_v_diff : Disjoint (c.u \ {c.pivot}) (c.v \ {c.pivot}) := by
   rw [disjoint_iff_inter_eq_empty]; ext p; simp [← h_inter]; tauto
lemma disj_middle : Disjoint ({c.pivot} ∪ (c.u \ {c.pivot})) (c.v \ {c.pivot}) := by
  rw [disjoint_union_left]; exact ⟨c.disj_piv_v, c.disj_u_v_diff⟩

def Others := c.all_black \ (c.u ∪ c.v)

lemma Others_def : c.Others = c.all_black \ (c.u ∪ c.v) := rfl

lemma partition_eq :
    c.all_black = {c.pivot} ∪ (c.u \ {c.pivot}) ∪ (c.v \ {c.pivot}) ∪ c.Others := by
  rw [← c.h_inter]; dsimp [Others]
  ext p
  have h_u : p ∈ c.u → p ∈ c.all_black := fun h => c.hu_sub h
  have h_v : p ∈ c.v → p ∈ c.all_black := fun h => c.hv_sub h
  simp only [mem_union, mem_inter, mem_sdiff]; tauto

lemma disj_others :
    Disjoint ({c.pivot} ∪ (c.u \ {c.pivot}) ∪ (c.v \ {c.pivot})) c.Others := by
  rw [disjoint_iff_inter_eq_empty]; ext p; rw [← h_inter]; simp [Others]; tauto

theorem total_labels_eq_sum :
    (targetsW c.u c.v c.all_black).card + (targetsN c.u c.v c.all_black).card +
    (targetsE c.u c.v c.all_black).card + (targetsS c.u c.v c.all_black).card
    = n + c.a + c.b + 1 := by
  let u := c.u; let v := c.v; let pivot := c.pivot; let all_black := c.all_black
  rw [sum_card_eq_sum_incidence]
  nth_rewrite 1 [c.partition_eq]
  rw [sum_union c.disj_others]
  rw [sum_union c.disj_middle]
  rw [sum_union c.disj_piv_u]
  have sum_pivot : ∑ x ∈ {pivot}, incidence_count u v all_black x = 4 := by
    rw [sum_singleton]
    exact incidence_count_of_pivot pivot c.h_inter (c.hu_sub c.pivot_mem_u)
  have sum_u : ∑ x ∈ u \ {pivot}, incidence_count u v all_black x = (c.a - 1) * 2 := by
    calc
       ∑ x ∈ u \ {pivot}, incidence_count u v all_black x
           = ∑ x ∈ u \ {pivot}, 2 := by
             apply sum_congr rfl
             intro x hx
             rw [← c.h_inter, mem_sdiff] at hx
             have hx_not_v : x ∉ v := by
              intro hv
              have : x ∈ u ∩ v := by rw [mem_inter]; exact ⟨hx.1, hv⟩
              tauto
             exact incidence_count_of_u_diff x hx.1 hx_not_v pivot
              c.h_inter c.hu_sub c.h_u_mono c.h_v_mono c.h_u_inj c.h_v_inj
        _ = (c.a - 1) * 2 := by
            simp; rw [card_sdiff, c.hu]; congr 1
            rw [singleton_inter_of_mem c.pivot_mem_u]; simp
  have sum_v : ∑ x ∈ v \ {pivot}, incidence_count u v all_black x = (c.b - 1) * 2 := by
    calc
      ∑ x ∈ v \ {pivot}, incidence_count u v all_black x
          = ∑ x ∈ v \ {pivot}, 2 := by
            apply sum_congr rfl
            intro x hx
            rw [← c.h_inter, mem_sdiff] at hx
            have hx_not_u : x ∉ u := by
              intro hu
              have : x ∈ u ∩ v := by rw [mem_inter]; exact ⟨hu, hx.1⟩
              tauto
            exact incidence_count_of_v_diff x hx.1 hx_not_u pivot
              c.h_inter c.hv_sub c.h_u_mono c.h_v_mono c.h_u_inj c.h_v_inj
        _ = (c.b - 1) * 2 := by
            simp; rw [card_sdiff, c.hv]; congr 1
            rw [singleton_inter_of_mem c.pivot_mem_v]; simp
  have sum_others : ∑ x ∈ c.Others, incidence_count u v all_black x = n - (c.a + c.b - 1) := by
    calc
      ∑ x ∈ c.Others, incidence_count u v all_black x
          = ∑ x ∈ c.Others, 1 := by
            apply sum_congr rfl
            intro x hx
            rw [Others, mem_sdiff, mem_union, not_or] at hx
            exact incidence_count_of_others x hx.1 hx.2.1 hx.2.2
              c.h_u_mono c.h_v_mono c.h_u_inj c.h_v_inj c.h_u_max c.h_v_max
      _ = c.Others.card := by simp
      _ = n - (c.a + c.b - 1) := by
          simp only [Others]; rw [card_sdiff]; rw [h_n]
          congr 1
          have h_reduction : (u ∪ v) ∩ all_black = u ∪ v :=
            inter_eq_left.mpr c.union_sub
          rw [h_reduction]; rw [card_union]
          rw [hu, hv, h_inter, card_singleton]

  rw [sum_pivot, sum_u, sum_v, sum_others]
  have h_le : c.a + c.b - 1 ≤ n := by
    calc
      c.a + c.b - 1 = (c.u ∪ c.v).card  := by
                        rw [card_union c.u c.v, c.hu, c.hv,c.h_inter, card_singleton]
      _             ≤ c.all_black.card  := card_le_card c.union_sub
      _             = n                 := c.h_n

  have ha := c.a_pos
  have hb := c.b_pos

  zify [ha, hb, h_le]
  omega

theorem labels_total_intersection :
    (targetsWin c.u c.v c.all_black).card + (targetsNin c.u c.v c.all_black).card +
    (targetsEin c.u c.v c.all_black).card + (targetsSin c.u c.v c.all_black).card
    ≥ n + c.a + c.b - 3 := by
  have h_sum_eq := total_labels_eq_sum c
  have hW : (targetsWin c.u c.v c.all_black).card + 1 ≥ (targetsW c.u c.v c.all_black).card :=
    Nat.le_add_of_sub_le (targetsWin_inequality c.u c.v c.all_black c.h_unique_y)
  have hN : (targetsNin c.u c.v c.all_black).card + 1 ≥ (targetsN c.u c.v c.all_black).card :=
    Nat.le_add_of_sub_le (targetsNin_inequality c.u c.v c.all_black c.h_unique_x)
  have hS : (targetsSin c.u c.v c.all_black).card + 1 ≥ (targetsS c.u c.v c.all_black).card :=
    Nat.le_add_of_sub_le (targetsSin_inequality c.u c.v c.all_black c.h_unique_x)
  have hE : (targetsEin c.u c.v c.all_black).card + 1 ≥ (targetsE c.u c.v c.all_black).card :=
    Nat.le_add_of_sub_le (targetsEin_inequality c.u c.v c.all_black c.h_unique_y)
  have ha_pos := c.a_pos
  have hb_pos := c.b_pos
  have h_total_ge_3 : 3 ≤ n + c.a + c.b := by
    have h_a_le_n : c.a ≤ n := calc
      c.a = c.u.card         := c.hu.symm
      _   ≤ c.all_black.card := card_le_card c.hu_sub
      _   = n                := c.h_n
    linarith
  zify [h_total_ge_3] at hW hN hE hS h_sum_eq ⊢
  linarith

noncomputable def validLabels : Finset (Label n) :=
  let to_W : Point n ↪ Label n := ⟨fun p => ⟨p, .W⟩, by intro a b h; injection h⟩
  let to_N : Point n ↪ Label n := ⟨fun p => ⟨p, .N⟩, by intro a b h; injection h⟩
  let to_E : Point n ↪ Label n := ⟨fun p => ⟨p, .E⟩, by intro a b h; injection h⟩
  let to_S : Point n ↪ Label n := ⟨fun p => ⟨p, .S⟩, by intro a b h; injection h⟩

  (targetsWin c.u c.v c.all_black).map to_W ∪
  (targetsNin c.u c.v c.all_black).map to_N ∪
  (targetsEin c.u c.v c.all_black).map to_E ∪
  (targetsSin c.u c.v c.all_black).map to_S

lemma card_validLabels :
    (validLabels c).card =
    (targetsWin c.u c.v c.all_black).card + (targetsNin c.u c.v c.all_black).card +
    (targetsEin c.u c.v c.all_black).card + (targetsSin c.u c.v c.all_black).card := by
  rw [validLabels]
  repeat rw [card_union_of_disjoint]
  · simp only [card_map]
  all_goals {
    rw [disjoint_left]
    intro x h1 h2
    simp only [mem_union, mem_map, Function.Embedding.coeFn_mk] at h1 h2
    rcases x with ⟨p, type⟩
    cases type <;> simp at h1 h2
  }

open Classical

lemma not_valid_label_X {n : ℕ} [NeZero n] (c : IntersectionSetup n) (l : Label n)
    (h_valid : l ∈ validLabels c) (h_type : l.type = .X) : False := by
  simp only [validLabels, mem_union, mem_map, or_assoc] at h_valid
  rcases h_valid with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩
  <;> simp at h_type

lemma matilda_covers_at_most_one (m : Matilda n c.all_black) :
    ({l ∈ validLabels c | covers m l}).card ≤ 1 := by
  rw [card_le_one_iff]
  intro l1 l2 hl1 hl2
  rw [mem_filter] at hl1 hl2
  obtain ⟨h_valid1, h_cov1⟩ := hl1; obtain ⟨h_valid2, h_cov2⟩ := hl2
  by_contra h_ne
  let p1 := l1.source; let t1 := l1.type; let p2 := l2.source; let t2 := l2.type
  have h_uniq_x := c.h_unique_x; have h_uniq_y := c.h_unique_y
  have get_props : ∀ l ∈ validLabels c,
      (l.type = .W → l.source ∈ targetsWin c.u c.v c.all_black) ∧
      (l.type = .N → l.source ∈ targetsNin c.u c.v c.all_black) ∧
      (l.type = .E → l.source ∈ targetsEin c.u c.v c.all_black) ∧
      (l.type = .S → l.source ∈ targetsSin c.u c.v c.all_black) := by
    intros l hl
    simp only [validLabels, mem_union, mem_map, or_assoc] at hl
    rcases hl with ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩
    <;> simp [hp]

  have props1 := get_props l1 h_valid1; have props2 := get_props l2 h_valid2
  cases h1 : l1.type <;> cases h2 : l2.type
  · have hp1 := props1.1 h1; have hp2 := props2.1 h2
    simp only [mem_targetsWin, mem_targetsW] at hp1 hp2
    simp [h1, h2] at h_cov1 h_cov2
    have h_p_ne : p1 ≠ p2 := by
      contrapose! h_ne
      rcases l1 with ⟨src1, type1⟩
      rcases l2 with ⟨src2, type2⟩
      simp only [Label.mk.injEq]
      constructor
      · exact h_ne
      · simp at h1 h2; rw [h1, h2]
    exact unique_label_W (m := m) (p := p1) (q := p2)
      (hp := hp1.1.1) (hq := hp2.1.1) (h_ne := h_p_ne)
      (hp_pos := hp1.2) (hq_pos := hp2.2)
      (hp_in := h_cov1) (hq_in := h_cov2)
      (h_unique_y := h_uniq_y)
  · have hW := props1.1 h1; have hN := props2.2.1 h2
    simp only [mem_targetsWin, mem_targetsW] at hW
    simp only [mem_targetsNin, mem_targetsN] at hN
    simp [h1, h2] at h_cov1 h_cov2
    apply disjoint_label_W_N (m := m) (u := c.u) (bw := p1) (bn := p2)
      (hbw := hW.1.1) (hbn := hN.1.1)
      (hbw_pos := hW.2) (hbn_pos := hN.2)
      (h_u_mono := c.u_mono_le) (h_u_inj := c.u_inj_y)
      (h_w_in := h_cov1) (h_n_in := h_cov2)
    · simp only [mem_regionWExtend] at hW; exact hW.1.2.1
    · simp only [mem_regionNExtend] at hN; exact hN.1.2.1
  · have hW := props1.1 h1; have hE := props2.2.2.1 h2
    simp only [mem_targetsWin, mem_targetsW] at hW
    simp only [mem_targetsEin, mem_targetsE] at hE
    simp [h1, h2] at h_cov1 h_cov2
    apply disjoint_label_W_E (m := m) (u := c.u) (v := c.v) (bw := p1) (be := p2)
      (hbw := hW.1.1) (hbw_pos := hW.2) (hbe_bound := hE.2)
      (h_u_mono := c.u_mono_le) (h_v_mono := c.v_mono_le)
      (h_u_inj := c.u_inj_y)
      (h_w_in := h_cov1) (h_e_in := h_cov2)
      (h_bw_reg := hW.1.2) (h_be_reg := hE.1.2)
  · have hW := props1.1 h1; have hS := props2.2.2.2 h2
    simp only [mem_targetsWin, mem_targetsW] at hW
    simp only [mem_targetsSin, mem_targetsS] at hS
    simp [h1, h2] at h_cov1 h_cov2
    apply disjoint_label_S_W (m := m) (v := c.v) (bs := p2) (bw := p1)
      (hbs := hS.1.1) (hbw := hW.1.1)
      (hbs_bound := hS.2) (hbw_pos := hW.2)
      (h_v_mono := c.v_mono_le) (h_v_inj := c.v_inj_y)
      (h_s_in := h_cov2) (h_w_in := h_cov1)
    · simp only [mem_regionSExtend] at hS; exact hS.1.2.2
    · simp only [mem_regionWExtend] at hW; exact hW.1.2.2
  · exact not_valid_label_X c l2 h_valid2 h2
  · have hN := props1.2.1 h1; have hW := props2.1 h2
    simp only [mem_targetsWin, mem_targetsW] at hW
    simp only [mem_targetsNin, mem_targetsN] at hN
    simp [h1, h2] at h_cov1 h_cov2
    apply disjoint_label_W_N (m := m) (u := c.u)  (bw := p2) (bn := p1)
      (hbw := hW.1.1) (hbn := hN.1.1)
      (hbw_pos := hW.2) (hbn_pos := hN.2)
      (h_u_mono := c.u_mono_le) (h_u_inj := c.u_inj_y)
      (h_w_in := h_cov2) (h_n_in := h_cov1)
    · simp only [mem_regionWExtend] at hW; exact hW.1.2.1
    · simp only [mem_regionNExtend] at hN; exact hN.1.2.1
  · have hp1 := props1.2.1 h1; have hp2 := props2.2.1 h2
    simp only [mem_targetsNin, mem_targetsN] at hp1 hp2
    simp [h1, h2] at h_cov1 h_cov2
    have h_p_ne : p1 ≠ p2 := by
      contrapose! h_ne
      rcases l1 with ⟨src1, type1⟩
      rcases l2 with ⟨src2, type2⟩
      simp only [Label.mk.injEq]
      constructor
      · exact h_ne
      · simp at h1 h2; rw [h1, h2]
    exact unique_label_N (m := m) (p := p1) (q := p2) (hp := hp1.1.1) (hq := hp2.1.1)
     (h_ne := h_p_ne) (hp_pos := hp1.2) (hq_pos := hp2.2)
     (hp_in := h_cov1) (hq_in := h_cov2) (h_unique_x := h_uniq_x)
  · have hN := props1.2.1 h1; have hE := props2.2.2.1 h2
    simp only [mem_targetsNin, mem_targetsN] at hN
    simp only [mem_targetsEin, mem_targetsE] at hE
    simp [h1, h2] at h_cov1 h_cov2
    apply disjoint_label_E_N (m := m) (v := c.v) (be := p2) (bn := p1)
      (hbe := hE.1.1) (hbn := hN.1.1)
      (hbe_bound := hE.2) (hbn_pos := hN.2)
      (h_v_mono := c.v_mono_le) (h_v_inj := c.v_inj_y)
      (h_e_in := h_cov2) (h_n_in := h_cov1)
    · simp only [mem_regionEExtend] at hE; exact hE.1.2.2
    · simp only [mem_regionNExtend] at hN; exact hN.1.2.2
  · have hN := props1.2.1 h1; have hS := props2.2.2.2 h2
    simp only [mem_targetsNin, mem_targetsN] at hN
    simp only [mem_targetsSin, mem_targetsS] at hS
    simp [h1, h2] at h_cov1 h_cov2
    apply disjoint_label_N_S (m := m) (u := c.u) (v := c.v) (bn := p1) (bs := p2)
      (hbn := hN.1.1)
      (hbn_pos := hN.2) (hbs_bound := hS.2)
      (h_u_mono := c.u_mono_le) (h_v_mono := c.v_mono_le)
      (h_v_inj := c.v_inj_y)
      (h_n_in := h_cov1) (h_s_in := h_cov2)
      (h_bn_reg := hN.1.2) (h_bs_reg := hS.1.2)
  · exact not_valid_label_X c l2 h_valid2 h2
  · have hE := props1.2.2.1 h1; have hW := props2.1 h2
    simp only [mem_targetsEin, mem_targetsE] at hE
    simp only [mem_targetsWin, mem_targetsW] at hW
    simp [h1, h2] at h_cov1 h_cov2
    exact disjoint_label_W_E (m := m) (u := c.u) (v := c.v) (bw := p2) (be := p1)
      (hbw := hW.1.1) (hbw_pos := hW.2) (hbe_bound := hE.2)
      (h_u_mono := c.u_mono_le) (h_v_mono := c.v_mono_le)
      (h_u_inj := c.u_inj_y) (h_w_in := h_cov2) (h_e_in := h_cov1)
      (h_bw_reg := hW.1.2) (h_be_reg := hE.1.2)
  · have hE := props1.2.2.1 h1; have hN := props2.2.1 h2
    simp only [mem_targetsEin, mem_targetsE] at hE
    simp only [mem_targetsNin, mem_targetsN] at hN
    simp [h1, h2] at h_cov1 h_cov2
    apply disjoint_label_E_N (m := m) (v := c.v) (be := p1) (bn := p2)
      (hbe := hE.1.1) (hbn := hN.1.1)
      (hbe_bound := hE.2) (hbn_pos := hN.2)
      (h_v_mono := c.v_mono_le) (h_v_inj := c.v_inj_y)
      (h_e_in := h_cov1) (h_n_in := h_cov2)
    · simp only [mem_regionEExtend] at hE; exact hE.1.2.2
    · simp only [mem_regionNExtend] at hN; exact hN.1.2.2
  · have hp1 := props1.2.2.1 h1; have hp2 := props2.2.2.1 h2
    simp only [mem_targetsEin, mem_targetsE] at hp1 hp2
    simp [h1, h2] at h_cov1 h_cov2
    have h_p_ne : p1 ≠ p2 := by
      contrapose! h_ne
      rcases l1 with ⟨src1, type1⟩
      rcases l2 with ⟨src2, type2⟩
      simp only [Label.mk.injEq]
      constructor
      · exact h_ne
      · simp at h1 h2; rw [h1, h2]
    exact unique_label_E (m := m) (p := p1) (q := p2) (hp := hp1.1.1) (hq := hp2.1.1)
      (h_ne := h_p_ne) (hp_bound := hp1.2) (hq_bound := hp2.2)
      (hp_in := h_cov1) (hq_in := h_cov2) (h_unique_y := h_uniq_y)
  · have hE := props1.2.2.1 h1; have hS := props2.2.2.2 h2
    simp only [mem_targetsEin, mem_targetsE] at hE
    simp only [mem_targetsSin, mem_targetsS] at hS
    simp [h1, h2] at h_cov1 h_cov2
    apply disjoint_label_E_S (m := m) (u := c.u) (be := p1) (bs := p2)
      (hbe := hE.1.1) (hbs := hS.1.1)
      (hbe_bound := hE.2) (hbs_bound := hS.2)
      (h_u_mono := c.u_mono_le) (h_u_inj := c.u_inj_y)
      (h_e_in := h_cov1) (h_s_in := h_cov2)
    · simp only [mem_regionEExtend] at hE; exact hE.1.2.1
    · simp only [mem_regionSExtend] at hS; exact hS.1.2.1
  · exact not_valid_label_X c l2 h_valid2 h2
  · have hS := props1.2.2.2 h1; have hW := props2.1 h2
    simp only [mem_targetsSin, mem_targetsS] at hS
    simp only [mem_targetsWin, mem_targetsW] at hW
    simp [h1, h2] at h_cov1 h_cov2
    apply disjoint_label_S_W (m := m) (v := c.v) (bs := p1) (bw := p2)
      (hbs := hS.1.1) (hbw := hW.1.1) (hbs_bound := hS.2) (hbw_pos := hW.2)
      (h_v_mono := c.v_mono_le) (h_v_inj := c.v_inj_y) (h_s_in := h_cov1) (h_w_in := h_cov2)
    · simp only [mem_regionSExtend] at hS; exact hS.1.2.2
    · simp only [mem_regionWExtend] at hW; exact hW.1.2.2
  · have hS := props1.2.2.2 h1; have hN := props2.2.1 h2
    simp only [mem_targetsSin, mem_targetsS] at hS
    simp only [mem_targetsNin, mem_targetsN] at hN
    simp [h1, h2] at h_cov1 h_cov2
    apply disjoint_label_N_S (m := m) (u := c.u) (v := c.v) (bn := p2) (bs := p1)
      (hbn := hN.1.1)
      (hbn_pos := hN.2) (hbs_bound := hS.2)
      (h_u_mono := c.u_mono_le) (h_v_mono := c.v_mono_le)
      (h_v_inj := c.v_inj_y)
      (h_n_in := h_cov2) (h_s_in := h_cov1)
      (h_bn_reg := hN.1.2) (h_bs_reg := hS.1.2)
  · have hS := props1.2.2.2 h1; have hE := props2.2.2.1 h2
    simp only [mem_targetsSin, mem_targetsS] at hS
    simp only [mem_targetsEin, mem_targetsE] at hE
    simp [h1, h2] at h_cov1 h_cov2
    apply disjoint_label_E_S (m := m) (u := c.u) (be := p2) (bs := p1)
      (hbe := hE.1.1) (hbs := hS.1.1)
      (hbe_bound := hE.2) (hbs_bound := hS.2)
      (h_u_mono := c.u_mono_le) (h_u_inj := c.u_inj_y)
      (h_e_in := h_cov2) (h_s_in := h_cov1)
    · simp only [mem_regionEExtend] at hE; exact hE.1.2.1
    · simp only [mem_regionSExtend] at hS; exact hS.1.2.1
  · have hp1 := props1.2.2.2 h1; have hp2 := props2.2.2.2 h2
    simp only [mem_targetsSin, mem_targetsS] at hp1 hp2
    simp [h1, h2] at h_cov1 h_cov2
    have h_p_ne : p1 ≠ p2 := by
      contrapose! h_ne
      rcases l1 with ⟨src1, type1⟩
      rcases l2 with ⟨src2, type2⟩
      simp only [Label.mk.injEq]
      constructor
      · exact h_ne
      · simp at h1 h2; rw [h1, h2]
    exact unique_label_S (m := m) (p := p1) (q := p2) (hp := hp1.1.1) (hq := hp2.1.1)
      (h_ne := h_p_ne) (hp_bound := hp1.2) (hq_bound := hp2.2)
      (hp_in := h_cov1) (hq_in := h_cov2) (h_unique_x := h_uniq_x)
  · exact not_valid_label_X c l2 h_valid2 h2
  case X.W | X.N | X.E | X.S | X.X =>
    exact not_valid_label_X c l1 h_valid1 h1

lemma grid_size_ge_two_of_label {source : Point n} {lbl : LabelType}
    (hl : { source := source, type := lbl } ∈ c.validLabels) : 2 ≤ n := by
  cases lbl <;>
  { simp only [validLabels, mem_targetsWin, mem_targetsW,
               mem_union, mem_map] at hl
    simp_all
    try omega
  }

lemma valid_label_pos_not_black {n : ℕ} [NeZero n] (c : IntersectionSetup n)
    (l : Label n) (hl : l ∈ validLabels c) : (label_pos l).2 ∉ c.all_black := by
  intro h_pos_black
  rcases l with ⟨source, type⟩
  have h_n_ge_2 := grid_size_ge_two_of_label c hl
  simp only [label_pos] at h_pos_black
  have h_src_black : source ∈ c.all_black := by
    simp only [validLabels, mem_targetsWin, mem_targetsW,
               mem_targetsNin, mem_targetsN,
               mem_targetsEin, mem_targetsE,
               mem_targetsSin, mem_targetsS,
               mem_union, mem_map] at hl
    rcases type <;> simp_all
  cases type
  · change (source.1, source.2 - 1) ∈ c.all_black at h_pos_black
    have h_eq : source = (source.1, source.2 - 1) := by
      apply c.h_unique_x source h_src_black _ h_pos_black; simp
    replace h_eq := (Prod.ext_iff.mp h_eq).2
    have h_pos : 0 < source.2.val := by
      simp only [validLabels, mem_union, mem_map] at hl
      rcases hl with h | h
      · simp at h; omega
      · simp at h
    apply (Fin.ext_iff).mp at h_eq
    have h_le : (1 : Fin n) ≤ source.2 := by
      simp [Fin.le_def]
      rw [Nat.mod_eq_of_lt h_n_ge_2]
      apply Nat.succ_le_of_lt
      simp [h_pos]
    rw [Fin.sub_val_of_le h_le] at h_eq
    have h_one_val : (1 : Fin n).val = 1 := by
      simp; rw [Nat.mod_eq_of_lt h_n_ge_2]
    omega
  · change (source.1 - 1, source.2) ∈ c.all_black at h_pos_black
    have h_eq : source = (source.1 - 1, source.2) := by
      apply c.h_unique_y source h_src_black (source.1 - 1, source.2)  h_pos_black
      simp
    replace h_eq := (Prod.ext_iff.mp h_eq).1
    have h_pos : 0 < source.1.val := by
      simp only [validLabels, mem_union, mem_map] at hl
      rcases hl with h | h
      · simp at h; omega
      · simp at h
    apply (Fin.ext_iff).mp at h_eq
    have h_le : (1 : Fin n) ≤ source.1 := by
      simp [Fin.le_def]
      rw [Nat.mod_eq_of_lt h_n_ge_2]
      apply Nat.succ_le_of_lt
      exact h_pos
    rw [Fin.sub_val_of_le h_le] at h_eq
    have h_one_val : (1 : Fin n).val = 1 := by
      simp; rw [Nat.mod_eq_of_lt h_n_ge_2]
    omega
  · change (source.1, source.2 + 1) ∈ c.all_black at h_pos_black
    have h_eq : source = (source.1, source.2 + 1) := by
      apply c.h_unique_x source h_src_black (source.1, source.2 + 1) h_pos_black
      simp
    replace h_eq := (Prod.ext_iff.mp h_eq).2
    have h_lt : source.2.val < n - 1 := by
      simp only [validLabels, mem_union, mem_map] at hl
      rcases hl with h | h
      · simp at h; linarith
      · simp at h
    apply (Fin.ext_iff).mp at h_eq
    rw [Fin.val_add] at h_eq
    simp at h_eq
    rw [Nat.mod_eq_of_lt (by omega)] at h_eq
    omega
  · change (source.1 + 1, source.2) ∈ c.all_black at h_pos_black
    have h_eq : source = (source.1 + 1, source.2) := by
      apply c.h_unique_y source h_src_black (source.1 + 1, source.2) h_pos_black
      simp
    replace h_eq := (Prod.ext_iff.mp h_eq).1
    have h_lt : source.1.val < n - 1 := by
      simp only [validLabels, mem_union, mem_map] at hl
      rcases hl with h | h
      · simp at h
      · simp at h; linarith
    apply (Fin.ext_iff).mp at h_eq
    rw [Fin.val_add] at h_eq
    simp at h_eq
    rw [Nat.mod_eq_of_lt (by omega)] at h_eq
    omega
  · exact (not_valid_label_X c { source := source, type := .X } hl rfl).elim

variable (matildas_partition : Finset (Matilda n c.all_black))
variable (h_partition : ∀ p : Point n, p ∉ c.all_black → ∃! m ∈ matildas_partition, m.mem p)

theorem matilda_count_ge_label_count
  (matildas_partition : Finset (Matilda n c.all_black))
  (h_partition : ∀ p : Point n, p ∉ c.all_black → ∃! m ∈ matildas_partition, m.mem p):
    (validLabels c).card ≤ matildas_partition.card := by
  let f : { l // l ∈ validLabels c } → { m // m ∈ matildas_partition } := fun ⟨l, hl⟩ =>
    have h_white : (label_pos l).2 ∉ c.all_black :=
      valid_label_pos_not_black c l hl
    let m_obj := (h_partition (label_pos l).2 h_white).choose
    have h_mem : m_obj ∈ matildas_partition :=
      (h_partition (label_pos l).2 h_white).choose_spec.1.1
    ⟨m_obj, h_mem⟩
  have f_inj : Function.Injective f := by
    intro x1 x2 h_eq
    rcases x1 with ⟨l1, hl1⟩; rcases x2 with ⟨l2, hl2⟩
    simp only [f, Subtype.mk.injEq] at h_eq
    set M1 := (h_partition (label_pos l1).2 (valid_label_pos_not_black c l1 hl1)).choose
    set M2 := (h_partition (label_pos l2).2 (valid_label_pos_not_black c l2 hl2)).choose
    have h_cov1 : covers M1 l1 :=
      (h_partition (label_pos l1).2 (valid_label_pos_not_black c l1 hl1)).choose_spec.1.2
    have h_cov2 : covers M2 l2 :=
      (h_partition (label_pos l2).2 (valid_label_pos_not_black c l2 hl2)).choose_spec.1.2
    rw [← h_eq] at h_cov2
    let labels_in_M1 := {l ∈ validLabels c | covers M1 l}
    have h_l1_in : l1 ∈ labels_in_M1 := by
      simp only [labels_in_M1]; rw [mem_filter]
      exact ⟨hl1, h_cov1⟩
    have h_l2_in : l2 ∈ labels_in_M1 := by
      simp only [labels_in_M1]; rw [mem_filter]
      exact ⟨hl2, h_cov2⟩
    have h_card_le_1 := matilda_covers_at_most_one c M1
    rw [card_le_one_iff] at h_card_le_1
    have h_l_eq : l1 = l2 := h_card_le_1 h_l1_in h_l2_in
    ext; exact h_l_eq
  rw [← Fintype.card_coe (validLabels c)]
  rw [← Fintype.card_coe matildas_partition]
  apply Fintype.card_le_of_injective f f_inj

theorem matildas_count_ge_intersection_bound
    (matildas_partition : Finset (Matilda n c.all_black))
    (h_partition : ∀ p : Point n, p ∉ c.all_black → ∃! m ∈ matildas_partition, m.mem p) :
    n + c.a + c.b - 3 ≤ matildas_partition.card := by
  have h_ge_labels := matilda_count_ge_label_count c matildas_partition h_partition
  rw [card_validLabels] at h_ge_labels
  have h_labels_bound := labels_total_intersection c
  exact Nat.le_trans h_labels_bound h_ge_labels

theorem intersection_case_final_bound
    (matildas_partition : Finset (Matilda n c.all_black))
    (h_partition : ∀ p : Point n, p ∉ c.all_black → ∃! m ∈ matildas_partition, m.mem p)
    (h_erdos_szekeres : n ≤ c.a * c.b) :
    n + (4 * n).sqrt - 3 ≤ matildas_partition.card := by
  have h_geom := matildas_count_ge_intersection_bound c matildas_partition h_partition
  have h_alg := am_gm_bound_nat c.a c.b n h_erdos_szekeres
  calc
    n + (4 * n).sqrt - 3
      ≤ n + (c.a + c.b) - 3       := Nat.sub_le_sub_right (Nat.add_le_add_left h_alg n) 3
    _ = n + c.a + c.b - 3         := by ring_nf
    _ ≤ matildas_partition.card   := h_geom

end IntersectionSetup

structure DisjointSetup (n : ℕ) [NeZero n] where
  u : Finset (Point n)
  v : Finset (Point n)
  all_black : Finset (Point n)
  a : ℕ
  b : ℕ

  hu : u.card = a
  hv : v.card = b
  hu_sub : u ⊆ all_black
  hv_sub : v ⊆ all_black
  h_n : all_black.card = n

  h_disj : Disjoint u v

  h_u_mono : ∀ p ∈ u, ∀ q ∈ u, px p < px q → py p < py q
  h_v_mono : ∀ p ∈ v, ∀ q ∈ v, px p < px q → py q < py p
  h_u_inj : ∀ p ∈ u, ∀ q ∈ u, px p = px q → p = q
  h_v_inj : ∀ p ∈ v, ∀ q ∈ v, px p = px q → p = q

  h_u_max : ∀ p ∈ all_black, p ∉ u →
      (∀ q ∈ u, px q < px p → py q < py p) →
      (∀ q ∈ u, px p < px q → py p < py q) → False
  h_v_max : ∀ p ∈ all_black, p ∉ v →
      (∀ q ∈ v, px q < px p → py p < py q) →
      (∀ q ∈ v, px p < px q → py q < py p) → False

  h_unique_x : ∀ p ∈ all_black, ∀ q ∈ all_black, px p = px q → p = q
  h_unique_y : ∀ p ∈ all_black, ∀ q ∈ all_black, py p = py q → p = q

namespace DisjointSetup

variable {n : ℕ} [NeZero n] (c : DisjointSetup n)

lemma u_mono_le : ∀ a ∈ c.u, ∀ b ∈ c.u, px a ≤ px b → py a ≤ py b :=
  chain_u_mono_le c.h_u_mono c.h_u_inj
lemma v_mono_le : ∀ a ∈ c.v, ∀ b ∈ c.v, px a ≤ px b → py b ≤ py a :=
  chain_v_mono_le c.h_v_mono c.h_v_inj
lemma u_inj_y : ∀ a ∈ c.u, ∀ b ∈ c.u, py a = py b → a = b :=
  chain_u_inj_y c.h_u_mono c.h_u_inj
lemma v_inj_y : ∀ a ∈ c.v, ∀ b ∈ c.v, py a = py b → a = b :=
  chain_v_inj_y c.h_v_mono c.h_v_inj

noncomputable def u_list : List (Point n) := c.u.toList.mergeSort ((· ≤ ·) on px)
noncomputable def v_list : List (Point n) := c.v.toList.mergeSort ((· ≤ ·) on px)

@[simp]
lemma u_list_length : c.u_list.length = c.a := by simp [u_list, c.hu]
@[simp]
lemma v_list_length : c.v_list.length = c.b := by simp [v_list, c.hv]
@[simp]
lemma mem_u_list (p : Point n) : p ∈ c.u_list ↔ p ∈ c.u := by simp [u_list]
@[simp]
lemma mem_v_list (p : Point n) : p ∈ c.v_list ↔ p ∈ c.v := by simp [v_list]

lemma u_list_sorted : c.u_list.Pairwise ((· ≤ ·) on px) := by
  rw [u_list]; simpa using List.pairwise_mergeSort
    (le := fun p q => px p ≤ px q)
    (fun _ _ _ => by simp; apply le_trans) (fun a b => by simp; apply le_total)
    c.u.toList
lemma v_list_sorted : c.v_list.Pairwise ((· ≤ ·) on px) := by
  rw [v_list]; simpa using List.pairwise_mergeSort
    (le := fun p q => px p ≤ px q)
    (fun _ _ _ => by simp; apply le_trans) (fun a b => by simp; apply le_total)
    c.v.toList
lemma u_list_ne_nil (ha_pos : 0 < c.a) : c.u_list ≠ [] := by
  rw [← List.length_pos_iff_ne_nil, u_list_length]; exact ha_pos
lemma v_list_ne_nil (hb_pos : 0 < c.b) : c.v_list ≠ [] := by
  rw [← List.length_pos_iff_ne_nil, v_list_length]; exact hb_pos
lemma u_list_nodup : c.u_list.Nodup := by
  rw [u_list]; exact (nodup_toList c.u).perm (List.mergeSort_perm _ _).symm
lemma v_list_nodup : c.v_list.Nodup := by
  rw [v_list]; exact (nodup_toList c.v).perm (List.mergeSort_perm _ _).symm

lemma head_le_of_mem_sorted {α : Type*} {l : List α} {r : α → α → Prop} [Std.Refl r]
    (h_sorted : l.Pairwise r) (h_ne : l ≠ []) (x : α) (hx : x ∈ l) :
    r (l.head h_ne) x := by
  cases l with
  | nil => contradiction
  | cons a tail =>
    rw [List.pairwise_cons] at h_sorted
    simp only [List.mem_cons] at hx
    rcases hx with rfl | h_in_tail
    · apply refl_of r
    · exact h_sorted.1 x h_in_tail

lemma last_le_of_mem_sorted {α : Type*} {l : List α} {r : α → α → Prop} [Std.Refl r]
    (h_sorted : l.Pairwise r) (h_ne : l ≠ []) (x : α) (hx : x ∈ l) :
    r x (l.getLast h_ne) := by
  cases l using List.reverseRecOn with
  | nil => contradiction
  | append_singleton xs a =>
    simp only [List.getLast_append_singleton]
    rw [List.pairwise_append] at h_sorted
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with h_in_xs | rfl
    · exact h_sorted.2.2 x h_in_xs a (List.mem_singleton_self a)
    · exact refl _

lemma px_head_le_of_mem_u (ha_pos : 0 < c.a) (q : Point n) (hq : q ∈ c.u) :
    px (c.u_list.head (c.u_list_ne_nil ha_pos)) ≤ px q := by
    apply head_le_of_mem_sorted c.u_list_sorted (c.u_list_ne_nil ha_pos)
    simpa using hq

lemma py_head_le_of_mem_u (ha_pos : 0 < c.a) (q : Point n) (hq : q ∈ c.u) :
    py (c.u_list.head (c.u_list_ne_nil ha_pos)) ≤ py q := by
  let u0 := c.u_list.head (c.u_list_ne_nil ha_pos)
  have h_u0_mem : u0 ∈ c.u := by rw [← mem_u_list]; exact List.head_mem _
  have hx_le : px u0 ≤ px q := c.px_head_le_of_mem_u ha_pos q hq
  rcases hx_le.lt_or_eq with h_lt | h_eq
  · have hy_lt : py u0 < py q := c.h_u_mono u0 h_u0_mem q hq h_lt
    exact le_of_lt hy_lt
  · have h_same : u0 = q := c.h_u_inj u0 h_u0_mem q hq h_eq
    subst h_same; exact le_refl _
lemma px_le_last_of_mem_u (ha_pos : 0 < c.a) (q : Point n) (hq : q ∈ c.u) :
    px q ≤ px (c.u_list.getLast (c.u_list_ne_nil ha_pos)) := by
  let u_last := c.u_list.getLast (c.u_list_ne_nil ha_pos)
  apply last_le_of_mem_sorted c.u_list_sorted (c.u_list_ne_nil ha_pos)
  simpa using hq

lemma py_le_last_of_mem_u (ha_pos : 0 < c.a) (q : Point n) (hq : q ∈ c.u) :
    py q ≤ py (c.u_list.getLast (c.u_list_ne_nil ha_pos)) := by
  let u_last := c.u_list.getLast (c.u_list_ne_nil ha_pos)
  have h_u_last_mem : u_last ∈ c.u := by rw [← mem_u_list]; apply List.getLast_mem
  have hx_le : px q ≤ px u_last := c.px_le_last_of_mem_u ha_pos q hq
  rcases hx_le.lt_or_eq with h_lt | h_eq
  · exact le_of_lt (c.h_u_mono q hq u_last h_u_last_mem h_lt)
  · have h_same : q = u_last := c.h_u_inj q hq u_last h_u_last_mem h_eq
    subst h_same; exact le_refl _

lemma px_head_le_of_mem_v (hb_pos : 0 < c.b) (q : Point n) (hq : q ∈ c.v) :
    px (c.v_list.head (c.v_list_ne_nil hb_pos)) ≤ px q := by
  apply head_le_of_mem_sorted c.v_list_sorted (c.v_list_ne_nil hb_pos)
  simpa using hq

lemma py_head_ge_of_mem_v (hb_pos : 0 < c.b) (q : Point n) (hq : q ∈ c.v) :
    py q ≤ py (c.v_list.head (c.v_list_ne_nil hb_pos)) := by
  let v0 := c.v_list.head (c.v_list_ne_nil hb_pos)
  have h_v0_mem : v0 ∈ c.v := by rw [← mem_v_list]; exact List.head_mem _
  have hx_le : px v0 ≤ px q := by
    apply head_le_of_mem_sorted c.v_list_sorted (c.v_list_ne_nil hb_pos)
    simpa using hq
  rcases hx_le.lt_or_eq with h_lt | h_eq
  · exact le_of_lt (c.h_v_mono v0 h_v0_mem q hq h_lt)
  · have h_same : v0 = q := c.h_v_inj v0 h_v0_mem q hq h_eq
    subst h_same
    exact le_refl _

lemma px_le_last_of_mem_v (hb_pos : 0 < c.b) (q : Point n) (hq : q ∈ c.v) :
    px q ≤ px (c.v_list.getLast (c.v_list_ne_nil hb_pos)) := by
  apply last_le_of_mem_sorted c.v_list_sorted (c.v_list_ne_nil hb_pos)
  simpa using hq

lemma py_ge_last_of_mem_v (hb_pos : 0 < c.b) (q : Point n) (hq : q ∈ c.v) :
    py (c.v_list.getLast (c.v_list_ne_nil hb_pos)) ≤ py q := by
  let v_last := c.v_list.getLast (c.v_list_ne_nil hb_pos)
  have h_vl_mem : v_last ∈ c.v := by rw [← mem_v_list]; exact List.getLast_mem _
  have hx_le : px q ≤ px v_last := c.px_le_last_of_mem_v hb_pos q hq
  rcases hx_le.lt_or_eq with h_lt | h_eq
  · exact le_of_lt (c.h_v_mono q hq v_last h_vl_mem h_lt)
  · rw [c.h_v_inj q hq v_last h_vl_mem h_eq]

lemma mem_of_mem_lower_of_mem_upper {p : Point n}
    (h_lo : p ∈ v_lower c.v) (h_up : p ∈ v_upper c.v) : p ∈ c.v := by
  rw [← v_parts_intersection_eq_v c.h_v_mono c.h_v_inj, mem_inter]
  exact ⟨h_lo, h_up⟩

lemma px_ne_of_mem_disjoint {p q : Point n} (hp : p ∈ c.u) (hq : q ∈ c.v) :
    px p ≠ px q := by
  intro h_eq
  have h_same : p = q := c.h_unique_x p (c.hu_sub hp) q (c.hv_sub hq) h_eq
  subst h_same
  exact disjoint_left.mp c.h_disj hp hq

lemma py_ne_of_mem_disjoint {p q : Point n} (hp : p ∈ c.u) (hq : q ∈ c.v) :
    py p ≠ py q := by
  intro h_eq
  have h_same : p = q := c.h_unique_y p (c.hu_sub hp) q (c.hv_sub hq) h_eq
  subst h_same
  exact disjoint_left.mp c.h_disj hp hq

syntax "contradict_max" term "using" term "," term "as" ident ident ident : tactic
macro_rules
  | `(tactic| contradict_max $max_hyp:term using $hp_blk:term, $not_mem:term as $q:ident $hq:ident $h_ord:ident) =>
    `(tactic| apply ($max_hyp) _ ($hp_blk) ($not_mem) <;> intro $q $hq $h_ord)
macro "solve_no_black" p:term "," hp:term "," max_hyp:term "using" b_x:term "," b_y:term : tactic =>
  `(tactic| (
    have h_not_mem : ($p) ∉ _ := fun h => by
      have h_bx := ($b_x) ($p) h
      have h_by := ($b_y) ($p) h
      linarith
    contradict_max ($max_hyp) using ($hp), h_not_mem as q hq h_ord
    all_goals (
      have h_bx := ($b_x) q hq
      have h_by := ($b_y) q hq
      linarith
    )
  ))

lemma no_black_left_down_of_u_head (ha_pos : 0 < c.a) (p : Point n)
    (hp : p ∈ c.all_black)
    (hx : px p < px (c.u_list.head (c.u_list_ne_nil ha_pos)))
    (hy : py p < py (c.u_list.head (c.u_list_ne_nil ha_pos))) : False := by
  solve_no_black p, hp, c.h_u_max using
    c.px_head_le_of_mem_u ha_pos, c.py_head_le_of_mem_u ha_pos
lemma no_black_right_up_of_u_last (ha_pos : 0 < c.a) (p : Point n)
    (hp : p ∈ c.all_black)
    (hx : px (c.u_list.getLast (c.u_list_ne_nil ha_pos)) < px p)
    (hy : py (c.u_list.getLast (c.u_list_ne_nil ha_pos)) < py p) : False := by
  solve_no_black p, hp, c.h_u_max using
    c.px_le_last_of_mem_u ha_pos, c.py_le_last_of_mem_u ha_pos
lemma no_black_left_up_of_v_head (hb_pos : 0 < c.b) (p : Point n)
    (hp : p ∈ c.all_black)
    (hx : px p < px (c.v_list.head (c.v_list_ne_nil hb_pos)))
    (hy : py (c.v_list.head (c.v_list_ne_nil hb_pos)) < py p) : False := by
  solve_no_black p, hp, c.h_v_max using
    c.px_head_le_of_mem_v hb_pos, c.py_head_ge_of_mem_v hb_pos
lemma no_black_right_down_of_v_last (hb_pos : 0 < c.b) (p : Point n)
    (hp : p ∈ c.all_black)
    (hx : px (c.v_list.getLast (c.v_list_ne_nil hb_pos)) < px p)
    (hy : py p < py (c.v_list.getLast (c.v_list_ne_nil hb_pos))) : False := by
  solve_no_black p, hp, c.h_v_max using
    c.px_le_last_of_mem_v hb_pos, c.py_ge_last_of_mem_v hb_pos

lemma u_head_mem_v_lower (ha_pos : 0 < c.a) :
    c.u_list.head (c.u_list_ne_nil ha_pos) ∈ v_lower c.v := by
  let u0 := c.u_list.head (c.u_list_ne_nil ha_pos)
  have h_in_u : u0 ∈ c.u := by rw [← mem_u_list]; exact List.head_mem _
  have h_not_v : u0 ∉ c.v := disjoint_left.mp c.h_disj h_in_u
  rcases covering_of_maximal_v u0 (c.hu_sub h_in_u) h_not_v c.h_v_max with h_lo | h_up
  · exact h_lo
  · exfalso
    rw [mem_v_upper] at h_up
    obtain ⟨vj, hvj, hx_le, hy_le⟩ := h_up
    have hx_lt : px vj < px u0 := hx_le.lt_of_ne <| by
      intro h_eq
      have : vj = u0 := c.h_unique_x vj (c.hv_sub hvj) u0 (c.hu_sub h_in_u) h_eq
      subst this; contradiction
    have hy_lt : py vj < py u0 := hy_le.lt_of_ne <| by
      intro h_eq
      have : vj = u0 := c.h_unique_y vj (c.hv_sub hvj) u0 (c.hu_sub h_in_u) h_eq
      subst this; contradiction
    exact c.no_black_left_down_of_u_head ha_pos vj (c.hv_sub hvj) hx_lt hy_lt

lemma u_last_mem_v_upper (ha_pos : 0 < c.a) :
    c.u_list.getLast (c.u_list_ne_nil ha_pos) ∈ v_upper c.v := by
  let u_last := c.u_list.getLast (c.u_list_ne_nil ha_pos)
  have h_in_u : u_last ∈ c.u := by rw [← mem_u_list]; exact List.getLast_mem _
  have h_not_v : u_last ∉ c.v := disjoint_left.mp c.h_disj h_in_u
  rcases covering_of_maximal_v u_last (c.hu_sub h_in_u) h_not_v c.h_v_max with h_lo | h_up
  · exfalso
    rw [mem_v_lower] at h_lo
    obtain ⟨vj, hvj, hx_le, hy_le⟩ := h_lo
    have hx_lt : px u_last < px vj := hx_le.lt_of_ne <| by
      intro h_eq
      have : u_last = vj := c.h_unique_x u_last (c.hu_sub h_in_u) vj (c.hv_sub hvj) h_eq
      subst this; contradiction
    have hy_lt : py u_last < py vj := hy_le.lt_of_ne <| by
      intro h_eq
      have : u_last = vj := c.h_unique_y u_last (c.hu_sub h_in_u) vj (c.hv_sub hvj) h_eq
      subst this; contradiction
    exact c.no_black_right_up_of_u_last ha_pos vj (c.hv_sub hvj) hx_lt hy_lt
  · exact h_up

lemma a_ge_two (ha_pos : 0 < c.a) : 2 ≤ c.a := by
  by_contra h_lt
  have h_len : c.u_list.length = 1 := by rw [c.u_list_length]; omega
  obtain ⟨u0, h_list⟩ := List.length_eq_one_iff.mp h_len
  have h_lo : u0 ∈ v_lower c.v := by simpa [h_list] using c.u_head_mem_v_lower ha_pos
  have h_up : u0 ∈ v_upper c.v := by simpa [h_list] using c.u_last_mem_v_upper ha_pos
  have h_in_v : u0 ∈ c.v := c.mem_of_mem_lower_of_mem_upper h_lo h_up
  have h_in_u : u0 ∈ c.u := by rw [← mem_u_list, h_list]; exact List.mem_singleton.mpr rfl
  exact disjoint_left.mp c.h_disj h_in_u h_in_v

lemma exists_crossing_u (ha_pos : 0 < c.a) :
    ∃ k : Fin (c.a - 1),
      (c.u_list.get ⟨k, by simp; omega⟩ ∈ v_lower c.v) ∧
      (c.u_list.get ⟨k + 1, by simp; omega⟩ ∈ v_upper c.v) := by
  let P := fun (i : ℕ) =>
    if h : i < c.a then
      c.u_list.get ⟨i, by simp; exact h⟩ ∈ v_lower c.v
    else False
  let valid_indices := (range c.a).filter P
  have h0_mem : 0 ∈ valid_indices := by
    simp [valid_indices, P, ha_pos]
    simpa [List.head_eq_getElem] using c.u_head_mem_v_lower ha_pos
  let i_idx := valid_indices.max' ⟨0, h0_mem⟩
  have hi_mem : i_idx ∈ valid_indices := max'_mem _ _
  simp only [valid_indices, mem_filter, mem_range] at hi_mem
  obtain ⟨hi_lt_a, hi_lower⟩ := hi_mem
  simp only [P, dif_pos hi_lt_a] at hi_lower
  have h_i_lt_last : i_idx < c.a - 1 := by
    by_contra h_ge
    have h_last : i_idx = c.a - 1 := by omega
    let u_last := c.u_list.getLast (c.u_list_ne_nil ha_pos)
    have h_lo : u_last ∈ v_lower c.v := by
      convert hi_lower
      simp [u_last, h_last, List.getLast_eq_getElem]
    have h_up : u_last ∈ v_upper c.v := c.u_last_mem_v_upper ha_pos
    have h_in_v : u_last ∈ c.v := c.mem_of_mem_lower_of_mem_upper h_lo h_up
    have h_in_u : u_last ∈ c.u := by rw [← mem_u_list]; exact List.getLast_mem _
    exact disjoint_left.mp c.h_disj h_in_u h_in_v

  use ⟨i_idx, h_i_lt_last⟩
  constructor
  · exact hi_lower
  · let next_idx := i_idx + 1
    have h_next_lt_a : next_idx < c.a := by omega
    let u_next := c.u_list.get ⟨next_idx, by simp; omega⟩

    have h_not_lo : u_next ∉ v_lower c.v := by
      intro h_in
      have : next_idx ∈ valid_indices := by
        simpa [valid_indices, P, h_next_lt_a] using h_in
      have : next_idx ≤ i_idx := le_max' _ _ this
      omega
    have h_next_mem_u : u_next ∈ c.u := by rw [← mem_u_list]; exact List.get_mem _ _
    have h_not_v : u_next ∉ c.v := disjoint_left.mp c.h_disj h_next_mem_u
    have h_next_blk : u_next ∈ c.all_black := c.hu_sub h_next_mem_u
    rcases covering_of_maximal_v u_next h_next_blk h_not_v c.h_v_max with h_lo | h_up
    · contradiction
    · exact h_up

lemma v_head_mem_u_upper (hb_pos : 0 < c.b) :
    c.v_list.head (c.v_list_ne_nil hb_pos) ∈ u_upper c.u := by
  let v0 := c.v_list.head (c.v_list_ne_nil hb_pos)
  have h_in_v : v0 ∈ c.v := by rw [← mem_v_list]; exact List.head_mem _
  have h_not_u : v0 ∉ c.u := disjoint_right.mp c.h_disj h_in_v
  rcases covering_of_maximal_u v0 (c.hv_sub h_in_v) h_not_u c.h_u_max with h_lo | h_up
  · exfalso
    rw [mem_u_lower] at h_lo
    obtain ⟨ui, hui, hx_le, hy_le⟩ := h_lo
    have hx_lt : px ui < px v0 := hx_le.lt_of_ne <| by
      intro h_eq
      have : ui = v0 := c.h_unique_x ui (c.hu_sub hui) v0 (c.hv_sub h_in_v) h_eq
      subst this; contradiction
    have hy_lt : py v0 < py ui := hy_le.lt_of_ne <| by
      intro h_eq
      have : ui = v0 := c.h_unique_y ui (c.hu_sub hui) v0 (c.hv_sub h_in_v) h_eq.symm
      subst this; contradiction
    exact c.no_black_left_up_of_v_head hb_pos ui (c.hu_sub hui) hx_lt hy_lt
  · exact h_up

lemma v_last_mem_u_lower (hb_pos : 0 < c.b) :
    c.v_list.getLast (c.v_list_ne_nil hb_pos) ∈ u_lower c.u := by
  let v_last := c.v_list.getLast (c.v_list_ne_nil hb_pos)
  have h_in_v : v_last ∈ c.v := by rw [← mem_v_list]; exact List.getLast_mem _
  have h_not_u : v_last ∉ c.u := disjoint_right.mp c.h_disj h_in_v
  rcases covering_of_maximal_u v_last (c.hv_sub h_in_v) h_not_u c.h_u_max with h_lo | h_up
  · exact h_lo
  · exfalso
    rw [mem_u_upper] at h_up
    obtain ⟨ui, hui, hx_le, hy_ge⟩ := h_up
    have hx_lt : px v_last < px ui := hx_le.lt_of_ne <| by
      intro h_eq
      have : v_last = ui := c.h_unique_x v_last (c.hv_sub h_in_v) ui (c.hu_sub hui) h_eq
      subst this; contradiction
    have hy_lt : py ui < py v_last := hy_ge.lt_of_ne <| by
      intro h_eq
      have : v_last = ui := c.h_unique_y v_last (c.hv_sub h_in_v) ui (c.hu_sub hui) h_eq.symm
      subst this; contradiction
    exact c.no_black_right_down_of_v_last hb_pos ui (c.hu_sub hui) hx_lt hy_lt

lemma b_ge_two (hb_pos : 0 < c.b) : 2 ≤ c.b := by
  by_contra h_lt
  have h_len : c.v_list.length = 1 := by rw [c.v_list_length]; omega
  obtain ⟨v0, h_list⟩ := List.length_eq_one_iff.mp h_len
  have h_up : v0 ∈ u_upper c.u := by simpa [h_list] using c.v_head_mem_u_upper hb_pos
  have h_lo : v0 ∈ u_lower c.u := by simpa [h_list] using c.v_last_mem_u_lower hb_pos
  have h_inter : v0 ∈ u_lower c.u  ∩ u_upper c.u := mem_inter.mpr ⟨h_lo, h_up⟩
  rw [u_parts_intersection_eq_u c.h_u_mono c.h_u_inj] at h_inter
  have h_in_v : v0 ∈ c.v := by rw [← mem_v_list, h_list]; exact List.mem_singleton.mpr rfl
  exact disjoint_right.mp c.h_disj h_in_v h_inter

lemma exists_crossing_v (hb_pos : 0 < c.b) :
    ∃ k : Fin (c.b - 1),
      (c.v_list.get ⟨k, by simp; omega⟩ ∈ u_upper c.u) ∧
      (c.v_list.get ⟨k + 1, by simp; omega⟩ ∈ u_lower c.u) := by
  let P := fun (j : ℕ) =>
    if h : j < c.b then
      c.v_list.get ⟨j, by simp; exact h⟩ ∈ u_upper c.u
    else False
  let valid_indices := (range c.b).filter P
  have h0_mem : 0 ∈ valid_indices := by
    simp [valid_indices, P, hb_pos]
    simpa [List.head_eq_getElem] using c.v_head_mem_u_upper hb_pos
  let j_idx := valid_indices.max' ⟨0, h0_mem⟩
  have hj_mem : j_idx ∈ valid_indices := max'_mem _ _
  simp only [valid_indices, mem_filter, mem_range] at hj_mem
  obtain ⟨hj_lt_b, hj_upper⟩ := hj_mem
  simp only [P, dif_pos hj_lt_b] at hj_upper
  have h_j_lt_last : j_idx < c.b - 1 := by
    by_contra h_ge
    have h_last : j_idx = c.b - 1 := by omega
    let v_last := c.v_list.getLast (c.v_list_ne_nil hb_pos)
    have h_up : v_last ∈ u_upper c.u := by
      convert hj_upper
      simp [v_last, h_last, List.getLast_eq_getElem]
    have h_lo : v_last ∈ u_lower c.u := c.v_last_mem_u_lower hb_pos
    have h_inter : v_last ∈ u_lower c.u ∩ u_upper c.u := mem_inter.mpr ⟨h_lo, h_up⟩
    rw [u_parts_intersection_eq_u c.h_u_mono c.h_u_inj] at h_inter
    have h_in_v : v_last ∈ c.v := by rw [← mem_v_list]; exact List.getLast_mem _
    exact disjoint_right.mp c.h_disj h_in_v h_inter

  use ⟨j_idx, h_j_lt_last⟩
  constructor
  · exact hj_upper
  · let next_idx := j_idx + 1
    have h_next_lt_b : next_idx < c.b := by omega
    let v_next := c.v_list.get ⟨next_idx, by simp; omega⟩

    have h_not_up : v_next ∉ u_upper c.u := by
      intro h_in
      have : next_idx ∈ valid_indices := by
        simpa [valid_indices, P, h_next_lt_b] using h_in
      have : next_idx ≤ j_idx := le_max' _ _ this
      omega

    have h_next_mem_v : v_next ∈ c.v := by rw [← mem_v_list]; exact List.get_mem _ _
    have h_not_u : v_next ∉ c.u := disjoint_right.mp c.h_disj h_next_mem_v
    have h_next_blk : v_next ∈ c.all_black := c.hv_sub h_next_mem_v
    rcases covering_of_maximal_u v_next h_next_blk h_not_u c.h_u_max with h_lo | h_up
    · exact h_lo
    · contradiction

structure CrossingPoints where
  k : Fin (c.a - 1)
  l : Fin (c.b - 1)
  uk  : Point n
  uk1 : Point n
  vl  : Point n
  vl1 : Point n
  h_uk  : uk  = c.u_list.get ⟨k, by simp; omega⟩
  h_uk1 : uk1 = c.u_list.get ⟨k + 1, by simp; omega⟩
  h_vl  : vl  = c.v_list.get ⟨l, by simp; omega⟩
  h_vl1 : vl1 = c.v_list.get ⟨l + 1, by simp; omega⟩
  h_uk_lo  : uk  ∈ v_lower c.v
  h_uk1_up : uk1 ∈ v_upper c.v
  h_vl_up  : vl  ∈ u_upper c.u
  h_vl1_lo : vl1 ∈ u_lower c.u
noncomputable def getCrossingPoints (ha_pos : 0 < c.a) (hb_pos : 0 < c.b) : CrossingPoints c :=
  let h_ex_u := c.exists_crossing_u ha_pos
  let k := Classical.choose h_ex_u
  let hk := Classical.choose_spec h_ex_u
  let h_ex_v := c.exists_crossing_v hb_pos
  let l := Classical.choose h_ex_v
  let hl := Classical.choose_spec h_ex_v
  {
    k := k, l := l
    uk := c.u_list.get ⟨k, by simp; omega⟩, uk1 := c.u_list.get ⟨k + 1, by simp; omega⟩
    vl := c.v_list.get ⟨l, by simp; omega⟩, vl1 := c.v_list.get ⟨l + 1, by simp; omega⟩
    h_uk := rfl, h_uk1 := rfl
    h_vl := rfl, h_vl1 := rfl
    h_uk_lo := hk.1, h_uk1_up := hk.2
    h_vl_up := hl.1, h_vl1_lo := hl.2
  }

variable (cp : CrossingPoints c)

def Pivot : Finset (Point n) :=
  let range_x := (Ico (px cp.uk) (px cp.uk1)) ∩ (Ico (px cp.vl) (px cp.vl1))
  let range_y := (Ico (py cp.uk) (py cp.uk1)) ∩ (Ico (py cp.vl1) (py cp.vl))
  univ.filter (fun p => px p ∈ range_x ∧ py p ∈ range_y)

lemma pivot_nonempty : (Pivot c cp).Nonempty := by
  let uk := cp.uk; let uk1 := cp.uk1; let vl := cp.vl; let vl1 := cp.vl1
  by_contra h_not_nonempty
  rw [not_nonempty_iff_eq_empty] at h_not_nonempty
  rw [Pivot] at h_not_nonempty
  rw [filter_eq_empty_iff] at h_not_nonempty
  let range_x := (Ico (px uk) (px uk1)) ∩ (Ico (px vl) (px vl1))
  let range_y := (Ico (py uk) (py uk1)) ∩ (Ico (py vl1) (py vl))
  have h_range_empty : range_x = ∅ ∨ range_y = ∅ := by
    by_contra h_both_nonempty; push_neg at h_both_nonempty
    obtain ⟨x, hx⟩ := h_both_nonempty.1
    obtain ⟨y, hy⟩ := h_both_nonempty.2
    have hx_lt : x < n := by
      rw [mem_inter] at hx; have := hx.1; rw [mem_Ico] at this
      exact lt_trans this.2 uk1.1.isLt
    have hy_lt : y < n := by
      rw [mem_inter] at hy; have := hy.1; rw [mem_Ico] at this
      exact lt_trans this.2 uk1.2.isLt
    let p : Point n := (⟨x, hx_lt⟩, ⟨y, hy_lt⟩)
    have hp_in : p ∈ Pivot c cp := by
      simp only [Pivot, mem_filter, mem_univ, true_and]
      exact ⟨hx, hy⟩
    rw [← filter_eq_empty_iff, ← not_nonempty_iff_eq_empty] at h_not_nonempty
    exact h_not_nonempty ⟨p, hp_in⟩
  have mem_uk : uk ∈ c.u := by simp only [uk]; rw[cp.h_uk, ← mem_u_list]; exact List.get_mem _ _
  have mem_uk1 : uk1 ∈ c.u := by
    simp only [uk1]; rw [cp.h_uk1, ← mem_u_list]; exact List.get_mem _ _
  have mem_vl : vl ∈ c.v := by
    simp only [vl]; rw [cp.h_vl, ← mem_v_list]; exact List.get_mem _ _
  have mem_vl1 : vl1 ∈ c.v := by
    simp only [vl1]; rw [cp.h_vl1, ← mem_v_list]; exact List.get_mem _ _
  rcases h_range_empty with h_x_empty | h_y_empty
  · simp only [range_x] at h_x_empty
    rw [Ico_inter_Ico, Ico_eq_empty_iff] at h_x_empty
    have h_u_lt : px uk < px uk1 := by
        have h_le : px uk ≤ px uk1 := by
           simp only [uk, uk1]; rw [cp.h_uk, cp.h_uk1]
           apply List.pairwise_iff_get.mp c.u_list_sorted
           simp
        have h_ne : uk ≠ uk1 := by
           simp only [uk, uk1]; rw [cp.h_uk, cp.h_uk1]
           intro h_eq
           have h_idx := (List.Nodup.get_inj_iff c.u_list_nodup).mp h_eq
           simp at h_idx
        apply lt_of_le_of_ne h_le
        intro h_px_eq
        apply h_ne
        exact c.h_u_inj uk mem_uk uk1 mem_uk1 h_px_eq
    have h_v_lt : px vl < px vl1 := by
      have h_le : px vl ≤ px vl1 := by
         simp only [vl, vl1]; rw [cp.h_vl, cp.h_vl1]
         apply List.pairwise_iff_get.mp c.v_list_sorted
         simp
      have h_ne : vl ≠ vl1 := by
        simp only [vl, vl1]; rw [cp.h_vl, cp.h_vl1]
        intro h_eq
        have h_idx := (List.Nodup.get_inj_iff c.v_list_nodup).mp h_eq
        simp at h_idx
      apply lt_of_le_of_ne h_le
      intro h_px_eq
      apply h_ne
      exact c.h_v_inj vl mem_vl vl1 mem_vl1 h_px_eq
    have h_split : px uk1 ≤ px vl ∨ px vl1 ≤ px uk := by
      by_contra h_not_or; push_neg at h_not_or
      push_neg at  h_x_empty
      simp only [min_le_iff, le_max_iff] at h_x_empty
      omega
    rcases h_split with h_le1 | h_le2
    · by_cases h_y : py uk1 ≤ py vl
      · have : uk1 ∈ v_lower c.v := by
          rw [mem_v_lower]; use vl
        have in_v : uk1 ∈ c.v := c.mem_of_mem_lower_of_mem_upper this cp.h_uk1_up
        exact disjoint_left.mp c.h_disj mem_uk1 in_v
      · push_neg at h_y
        have : vl ∈ u_lower c.u := by
          rw [mem_u_lower]; use uk1; exact ⟨mem_uk1, h_le1, le_of_lt h_y⟩
        have in_u : vl ∈ c.u := by
          have h_both : vl ∈ u_lower c.u ∩ u_upper c.u :=
            mem_inter.mpr ⟨this, cp.h_vl_up⟩
          rw [u_parts_intersection_eq_u c.h_u_mono c.h_u_inj] at h_both
          exact h_both
        exact disjoint_right.mp c.h_disj mem_vl in_u
    · by_cases h_y : py vl1 ≤ py uk
      · have : uk ∈ v_upper c.v := by
          rw [mem_v_upper]; use vl1
        have in_v : uk ∈ c.v := c.mem_of_mem_lower_of_mem_upper cp.h_uk_lo this
        exact disjoint_left.mp c.h_disj mem_uk in_v
      · push_neg at h_y
        have : vl1 ∈ u_upper c.u := by
          rw [mem_u_upper]; use uk; exact ⟨mem_uk, h_le2, le_of_lt h_y⟩
        have in_u : vl1 ∈ c.u := by
          have h_both : vl1 ∈ u_lower c.u ∩ u_upper c.u :=
            mem_inter.mpr ⟨cp.h_vl1_lo, this⟩
          rw [u_parts_intersection_eq_u c.h_u_mono c.h_u_inj] at h_both
          exact h_both
        exact disjoint_right.mp c.h_disj mem_vl1 in_u
  · simp only [range_y] at h_y_empty
    rw [Ico_inter_Ico, Ico_eq_empty_iff] at h_y_empty
    have h_u_py_lt : py uk < py uk1 := by
      have h_x_le : px uk ≤ px uk1 := by
         simp only [uk, uk1]; rw [cp.h_uk, cp.h_uk1]
         apply List.pairwise_iff_get.mp c.u_list_sorted; simp
      have h_x_ne : uk ≠ uk1 := by
         simp only [uk, uk1]; rw [cp.h_uk, cp.h_uk1]
         intro h
         have h_idx := (List.Nodup.get_inj_iff c.u_list_nodup).mp h
         simp at h_idx
      have h_x_lt : px uk < px uk1 := by
         apply lt_of_le_of_ne h_x_le
         intro h_eq
         exact h_x_ne (c.h_u_inj uk mem_uk uk1 mem_uk1 h_eq)
      exact c.h_u_mono uk mem_uk uk1 mem_uk1 h_x_lt
    have h_v_py_lt : py vl1 < py vl := by
      have h_x_le : px vl ≤ px vl1 := by
         simp only [vl, vl1]; rw [cp.h_vl, cp.h_vl1]
         apply List.pairwise_iff_get.mp c.v_list_sorted; simp
      have h_x_ne : vl ≠ vl1 := by
         simp only [vl, vl1]; rw [cp.h_vl, cp.h_vl1]
         intro h
         have h_idx :=  (List.Nodup.get_inj_iff c.v_list_nodup).mp h
         simp at h_idx
      have h_x_lt : px vl < px vl1 := by
         apply lt_of_le_of_ne h_x_le
         intro h_eq
         exact h_x_ne (c.h_v_inj vl mem_vl vl1 mem_vl1 h_eq)
      exact c.h_v_mono vl mem_vl vl1 mem_vl1 h_x_lt
    have h_split : py uk1 ≤ py vl1 ∨ py vl ≤ py uk := by
      by_contra h_not_or; push_neg at h_not_or; push_neg at h_y_empty
      simp only [min_le_iff, le_max_iff] at h_y_empty
      omega
    rcases h_split with h_le1 | h_le2
    · by_cases h_x : px uk1 ≤ px vl1
      · have : uk1 ∈ v_lower c.v := by rw [mem_v_lower]; use vl1
        have in_v : uk1 ∈ c.v := c.mem_of_mem_lower_of_mem_upper this cp.h_uk1_up
        exact disjoint_left.mp c.h_disj mem_uk1 in_v
      · push_neg at h_x
        have : vl1 ∈ u_upper c.u := by
           rw [mem_u_upper]; use uk1; exact ⟨mem_uk1, le_of_lt h_x, h_le1⟩
        have in_u : vl1 ∈ c.u := by
          have h_both : vl1 ∈ u_lower c.u ∩ u_upper c.u :=
             mem_inter.mpr ⟨cp.h_vl1_lo, this⟩
          rw [u_parts_intersection_eq_u c.h_u_mono c.h_u_inj] at h_both
          exact h_both
        exact disjoint_right.mp c.h_disj mem_vl1 in_u
    · by_cases h_x : px vl ≤ px uk
      · have : uk ∈ v_upper c.v := by
          rw [mem_v_upper]; use vl
        have in_v : uk ∈ c.v := c.mem_of_mem_lower_of_mem_upper cp.h_uk_lo this
        exact disjoint_left.mp c.h_disj mem_uk in_v
      · push_neg at h_x
        have : vl ∈ u_lower c.u := by
          rw [mem_u_lower]; use uk; exact ⟨mem_uk, le_of_lt h_x, h_le2⟩
        have in_u : vl ∈ c.u := by
          have h_both : vl ∈ u_lower c.u ∩ u_upper c.u :=
             mem_inter.mpr ⟨this, cp.h_vl_up⟩
          rw [u_parts_intersection_eq_u c.h_u_mono c.h_u_inj] at h_both
          exact h_both
        exact disjoint_right.mp c.h_disj mem_vl in_u

lemma not_mem_of_strictly_between_sorted {α : Type*} {r : α → α → Prop} [Std.Refl r]
    (L : List α) (h_sorted : L.Pairwise r)
    (k : Fin L.length) (k_next : Fin L.length) (h_adj : k.1 + 1 = k_next.1)
    (p : α) (hp : p ∈ L)
    (val : α → ℕ)
    (rel_val : ∀ x y, r x y → val x ≤ val y)
    (h_between : val (L.get k) < val p ∧ val p < val (L.get k_next)) :
    False := by
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hp
  by_cases h_le : i.1 ≤ k.1
  · have h_idx_le : i ≤ k := by simp [Fin.le_iff_val_le_val, h_le]
    have : r (L.get i) (L.get k) :=
      List.Pairwise.rel_get_of_le h_sorted h_idx_le
    have : val (L.get i) ≤ val (L.get k) := rel_val _ _ this
    linarith [h_between.1]
  · push_neg at h_le
    have h_ge : k_next.1 ≤ i.1 := by rw [← h_adj]; omega
    have h_idx_ge : k_next ≤ i := by simp [Fin.le_iff_val_le_val, h_ge]
    have : r (L.get k_next) (L.get i) :=
      List.Pairwise.rel_get_of_le h_sorted h_idx_ge
    have : val (L.get k_next) ≤ val (L.get i) := rel_val _ _ this
    linarith [h_between.2]

lemma pivot_no_black (cp : CrossingPoints c) :
    ∀ p ∈ Pivot c cp, p ∉ c.all_black := by
  let uk := cp.uk; let uk1 := cp.uk1
  let vl := cp.vl; let vl1 := cp.vl1
  have mem_uk : uk ∈ c.u := by
    rw [← c.mem_u_list]; dsimp only [uk]; rw[cp.h_uk]; apply List.get_mem
  have mem_uk1 : uk1 ∈ c.u := by
    rw [← c.mem_u_list]; dsimp only [uk1]; rw[cp.h_uk1]; apply List.get_mem
  have mem_vl : vl ∈ c.v := by
    rw [← c.mem_v_list]; dsimp only [vl]; rw[cp.h_vl]; apply List.get_mem
  have mem_vl1 : vl1 ∈ c.v := by
    rw [← c.mem_v_list]; dsimp only [vl1]; rw[cp.h_vl1]; apply List.get_mem
  intro p hp_piv hp_blk
  rw [Pivot, mem_filter] at hp_piv
  obtain ⟨_, ⟨hx_range, hy_range⟩⟩ := hp_piv
  rw [mem_inter, mem_Ico, mem_Ico] at hx_range
  rw [mem_inter, mem_Ico, mem_Ico] at hy_range
  obtain ⟨h_px_u_le, h_px_u_lt⟩ := hx_range.1
  obtain ⟨h_py_u_le, h_py_u_lt⟩ := hy_range.1
  obtain ⟨h_px_v_le, h_px_v_lt⟩ := hx_range.2
  obtain ⟨h_py_v_le, h_py_v_lt⟩ := hy_range.2
  have h_p_eq_uk : p = uk := by
    rcases lt_or_eq_of_le h_px_u_le with h_px_strict | h_px_eq
    · rcases lt_or_eq_of_le h_py_u_le with h_py_strict | h_py_eq
      · exfalso
        have h_p_not_in_u : p ∉ c.u := by
          intro h_in
          let k_idx : Fin c.u_list.length := ⟨cp.k, by simp; omega⟩
          let k1_idx : Fin c.u_list.length := ⟨cp.k + 1, by simp; omega⟩
          apply not_mem_of_strictly_between_sorted c.u_list c.u_list_sorted k_idx k1_idx rfl p
          · rwa [c.mem_u_list]
          · intro x y h; exact h
          · rw[← cp.h_uk, ← cp.h_uk1]; exact ⟨h_px_strict, h_px_u_lt⟩
        apply c.h_u_max p hp_blk h_p_not_in_u
        · intro q hq hq_lt_p
          have h_qx_le : px q ≤ px uk := by
             by_contra h_gt; push_neg at h_gt
             have h_q_lt_uk1 : px q < px uk1 := lt_trans hq_lt_p h_px_u_lt
             let k_idx : Fin c.u_list.length := ⟨cp.k, by simp; omega⟩
             let k1_idx : Fin c.u_list.length := ⟨cp.k + 1, by simp; omega⟩
             apply not_mem_of_strictly_between_sorted c.u_list c.u_list_sorted k_idx k1_idx rfl q
             · rwa [c.mem_u_list]
             · intro x y h; exact h
             · rw [← cp.h_uk, ← cp.h_uk1]; exact ⟨h_gt, h_q_lt_uk1⟩
          have : py q ≤ py uk := by
            rcases lt_or_eq_of_le h_qx_le with h_lt | h_eq
            · exact le_of_lt (c.h_u_mono q hq uk mem_uk h_lt)
            · rw [c.h_u_inj q hq uk mem_uk h_eq]
          exact lt_of_le_of_lt this h_py_strict
        · intro q hq hp_lt_q
          have h_qx_ge : px uk1 ≤ px q := by
             by_contra h_lt; push_neg at h_lt
             have h_uk_lt_q : px uk < px q := lt_trans h_px_strict hp_lt_q
             let k_idx : Fin c.u_list.length := ⟨cp.k, by simp; omega⟩
             let k1_idx : Fin c.u_list.length := ⟨cp.k + 1, by simp; omega⟩
             apply not_mem_of_strictly_between_sorted c.u_list c.u_list_sorted k_idx k1_idx rfl q
             · rwa [c.mem_u_list]
             · intro x y h; exact h
             · rw [← cp.h_uk, ← cp.h_uk1]; exact ⟨h_uk_lt_q, h_lt⟩
          have : py uk1 ≤ py q := by
            rcases lt_or_eq_of_le h_qx_ge with h_lt | h_eq
            · exact le_of_lt (c.h_u_mono uk1 mem_uk1 q hq h_lt)
            · rw [c.h_u_inj uk1 mem_uk1 q hq h_eq]
          exact lt_of_lt_of_le h_py_u_lt this
      · exact c.h_unique_y p hp_blk uk (c.hu_sub mem_uk) h_py_eq.symm
    · exact c.h_unique_x p hp_blk uk (c.hu_sub mem_uk) h_px_eq.symm
  have h_p_eq_vl : p = vl := by
    rcases lt_or_eq_of_le h_px_v_le with h_px_strict | h_px_eq
    · rcases lt_or_eq_of_le h_py_v_le with h_py_strict | h_py_eq
      · exfalso
        have h_p_not_in_v : p ∉ c.v := by
          intro h_in
          let l_idx : Fin c.v_list.length := ⟨cp.l, by simp; omega⟩
          let l1_idx : Fin c.v_list.length := ⟨cp.l + 1, by simp; omega⟩
          apply not_mem_of_strictly_between_sorted c.v_list c.v_list_sorted l_idx l1_idx rfl p
          · rwa [c.mem_v_list]
          · intro x y h; exact h
          · rw [← cp.h_vl, ← cp.h_vl1]; exact ⟨h_px_strict, h_px_v_lt⟩
        apply c.h_v_max p hp_blk h_p_not_in_v
        · intro q hq hq_lt_p
          have h_qx_le : px q ≤ px vl := by
             by_contra h_gt; push_neg at h_gt
             have h_q_lt_vl1 : px q < px vl1 := lt_trans hq_lt_p h_px_v_lt
             let l_idx : Fin c.v_list.length := ⟨cp.l, by simp; omega⟩
             let l1_idx : Fin c.v_list.length := ⟨cp.l + 1, by simp; omega⟩
             apply not_mem_of_strictly_between_sorted c.v_list c.v_list_sorted l_idx l1_idx rfl q
             · rwa [c.mem_v_list]
             · intro x y h; exact h
             · rw [← cp.h_vl, ← cp.h_vl1]; exact ⟨h_gt, h_q_lt_vl1⟩
          have : py vl ≤ py q := by
             rcases lt_or_eq_of_le h_qx_le with h_lt | h_eq
             · exact le_of_lt (c.h_v_mono q hq vl mem_vl h_lt)
             · rw [c.h_v_inj q hq vl mem_vl h_eq]
          exact lt_of_lt_of_le h_py_v_lt this
        · intro q hq hp_lt_q
          have h_qx_ge : px vl1 ≤ px q := by
             by_contra h_lt; push_neg at h_lt
             have h_vl_lt_q : px vl < px q := lt_trans h_px_strict hp_lt_q
             let l_idx : Fin c.v_list.length := ⟨cp.l, by simp; omega⟩
             let l1_idx : Fin c.v_list.length := ⟨cp.l + 1, by simp; omega⟩
             apply not_mem_of_strictly_between_sorted c.v_list c.v_list_sorted l_idx l1_idx rfl q
             · rwa [c.mem_v_list]
             · intro x y h; exact h
             · rw [← cp.h_vl, ← cp.h_vl1]; exact ⟨h_vl_lt_q, h_lt⟩
          have : py q ≤ py vl1 := by
             rcases lt_or_eq_of_le h_qx_ge with h_lt | h_eq
             · exact le_of_lt (c.h_v_mono vl1 mem_vl1 q hq h_lt)
             · rw [c.h_v_inj vl1 mem_vl1 q hq h_eq]
          exact lt_of_le_of_lt this h_py_strict
      · exfalso
        have h_p_eq_vl1 : p = vl1 :=
          c.h_unique_y p hp_blk vl1 (c.hv_sub mem_vl1) h_py_eq.symm
        rw [h_p_eq_vl1] at h_px_v_lt
        exact (lt_self_iff_false _).mp h_px_v_lt
    · exact c.h_unique_x p hp_blk vl (c.hv_sub mem_vl) h_px_eq.symm
  have h_eq : uk = vl := by rw [←h_p_eq_uk, h_p_eq_vl]
  have h_uk_in_v : uk ∈ c.v := by rw [h_eq]; exact mem_vl
  have h_uk_not_in_v : uk ∉ c.v := disjoint_left.mp c.h_disj mem_uk
  contradiction

lemma incidence_count_of_u_disjoint
    (p : Point n) (hp : p ∈ c.u) :
    incidence_count c.u c.v c.all_black p = 2 := by
  have h_lo : p ∈ u_lower c.u := by rw [mem_u_lower]; exact ⟨p, hp, le_refl _, le_refl _⟩
  have h_up : p ∈ u_upper c.u := by rw [mem_u_upper]; exact ⟨p, hp, le_refl _, le_refl _⟩
  have hp_not_v : p ∉ c.v := disjoint_left.mp c.h_disj hp
  have h_cover := covering_of_maximal_v p (c.hu_sub hp) hp_not_v c.h_v_max
  have h_excl : ¬(p ∈ v_lower c.v ∧ p ∈ v_upper c.v) := by
    intro h; rw [← mem_inter] at h
    rw [v_parts_intersection_eq_v c.h_v_mono c.h_v_inj] at h
    exact hp_not_v h
  have hp_all : p ∈ c.all_black := c.hu_sub hp
  simp only [incidence_count, mem_targetsW, mem_targetsN, mem_targetsS, mem_targetsE,
             mem_regionWExtend, mem_regionNExtend, mem_regionEExtend, mem_regionSExtend]
  simp only [hp_all, h_lo, h_up, true_and]
  rcases h_cover with h_v_lo | h_v_up
  · have h_not_up : p ∉ v_upper c.v := fun h => h_excl ⟨h_v_lo, h⟩
    simp [h_v_lo, h_not_up]
  · have h_not_lo : p ∉ v_lower c.v := fun h => h_excl ⟨h, h_v_up⟩
    simp [h_v_up, h_not_lo]

lemma incidence_count_of_v_disjoint
    (p : Point n) (hp : p ∈ c.v) :
    incidence_count c.u c.v c.all_black p = 2 := by
  have h_lo : p ∈ v_lower c.v := by rw [mem_v_lower]; exact ⟨p, hp, le_refl _, le_refl _⟩
  have h_up : p ∈ v_upper c.v := by rw [mem_v_upper]; exact ⟨p, hp, le_refl _, le_refl _⟩
  have hp_not_u : p ∉ c.u := disjoint_right.mp c.h_disj hp
  have h_cover := covering_of_maximal_u p (c.hv_sub hp) hp_not_u c.h_u_max
  have h_excl : ¬(p ∈ u_lower c.u ∧ p ∈ u_upper c.u) := by
    intro h; rw [← mem_inter] at h
    rw [u_parts_intersection_eq_u c.h_u_mono c.h_u_inj] at h
    exact hp_not_u h
  have hp_all : p ∈ c.all_black := c.hv_sub hp
  simp only [incidence_count, mem_targetsW, mem_targetsN, mem_targetsS, mem_targetsE,
             mem_regionWExtend, mem_regionNExtend, mem_regionEExtend, mem_regionSExtend]
  simp only [hp_all, h_lo, h_up]
  rcases h_cover with h_u_lo | h_u_up
  · have h_not_up : p ∉ u_upper c.u := fun h => h_excl ⟨h_u_lo, h⟩
    simp [h_u_lo, h_not_up]
  · have h_not_lo : p ∉ u_lower c.u := fun h => h_excl ⟨h, h_u_up⟩
    simp [h_u_up, h_not_lo]

theorem total_labels_eq_sum_disjoint :
    (targetsW c.u c.v c.all_black).card + (targetsN c.u c.v c.all_black).card +
    (targetsE c.u c.v c.all_black).card + (targetsS c.u c.v c.all_black).card
    = n + c.a + c.b := by
  rw [sum_card_eq_sum_incidence]
  let others := c.all_black \ (c.u ∪ c.v)
  have h_disj_uv : Disjoint c.u c.v := c.h_disj
  have h_disj_others : Disjoint (c.u ∪ c.v) others := disjoint_sdiff_self_right
  have h_union : c.all_black = c.u ∪ c.v ∪ others := by
    exact (union_sdiff_of_subset (union_subset c.hu_sub c.hv_sub)).symm
  nth_rewrite 1 [h_union]
  rw [sum_union h_disj_others]
  rw [sum_union h_disj_uv]
  have sum_u : ∑ x ∈ c.u, incidence_count c.u c.v c.all_black x = 2 * c.a := by
    rw [sum_congr rfl (fun x hx => incidence_count_of_u_disjoint c x hx)]
    simp [c.hu, mul_comm]
  have sum_v : ∑ x ∈ c.v, incidence_count c.u c.v c.all_black x = 2 * c.b := by
    rw [sum_congr rfl (fun x hx => incidence_count_of_v_disjoint c x hx)]
    simp [c.hv, mul_comm]
  have sum_others : ∑ x ∈ others, incidence_count c.u c.v c.all_black x = n - (c.a + c.b) := by
    calc
      ∑ x ∈ others, incidence_count c.u c.v c.all_black x
          = ∑ x ∈ others, 1 := by
            apply sum_congr rfl
            intro x hx
            simp only [others, mem_sdiff, mem_union, not_or] at hx
            exact incidence_count_of_others x hx.1 hx.2.1 hx.2.2
              c.h_u_mono c.h_v_mono c.h_u_inj c.h_v_inj c.h_u_max c.h_v_max
      _ = others.card := by simp
      _ = n - (c.a + c.b) := by
          simp only [others]; rw [card_sdiff]; rw [h_n]
          congr 1
          rw [inter_eq_left.mpr (union_subset c.hu_sub c.hv_sub)]
          rw [card_union_of_disjoint c.h_disj]
          rw [c.hu, c.hv]
  rw [sum_u, sum_v, sum_others]
  have h_le : c.a + c.b ≤ n := calc
    c.a + c.b = c.u.card + c.v.card := by rw [c.hu, c.hv]
    _         = (c.u ∪ c.v).card    := by rw [card_union_of_disjoint c.h_disj]
    _         ≤ c.all_black.card    := card_le_card (union_subset c.hu_sub c.hv_sub)
    _         = n                   := c.h_n
  omega

theorem labels_total_disjoint (ha_pos : 0 < c.a) (hb_pos : 0 < c.b) :
    (targetsWin c.u c.v c.all_black).card + (targetsNin c.u c.v c.all_black).card +
    (targetsEin c.u c.v c.all_black).card + (targetsSin c.u c.v c.all_black).card
    + 1
    ≥ n + c.a + c.b - 3 := by
  have h_sum_eq := total_labels_eq_sum_disjoint c
  have hW : (targetsWin c.u c.v c.all_black).card + 1 ≥ (targetsW c.u c.v c.all_black).card :=
    Nat.le_add_of_sub_le (targetsWin_inequality c.u c.v c.all_black c.h_unique_y)
  have hN : (targetsNin c.u c.v c.all_black).card + 1 ≥ (targetsN c.u c.v c.all_black).card :=
    Nat.le_add_of_sub_le (targetsNin_inequality c.u c.v c.all_black c.h_unique_x)
  have hS : (targetsSin c.u c.v c.all_black).card + 1 ≥ (targetsS c.u c.v c.all_black).card :=
    Nat.le_add_of_sub_le (targetsSin_inequality c.u c.v c.all_black c.h_unique_x)
  have hE : (targetsEin c.u c.v c.all_black).card + 1 ≥ (targetsE c.u c.v c.all_black).card :=
    Nat.le_add_of_sub_le (targetsEin_inequality c.u c.v c.all_black c.h_unique_y)
  zify [hW, hN, hS, hE, h_sum_eq]
  have ha_ge_2 := c.a_ge_two ha_pos
  have hb_ge_2 := c.b_ge_two hb_pos
  have h_total_ge_3 : 3 ≤ n + c.a + c.b := by linarith
  zify [h_total_ge_3] at hW hN hE hS h_sum_eq ⊢
  linarith

noncomputable def wx (cp : CrossingPoints c) : Point n :=
  (c.pivot_nonempty cp).choose

lemma wx_mem_pivot (cp : CrossingPoints c) : c.wx cp ∈ Pivot c cp :=
  (c.pivot_nonempty cp).choose_spec

lemma wx_bounds (cp : CrossingPoints c) :
    let p := c.wx cp
    (px cp.uk ≤ px p ∧ px p < px cp.uk1) ∧
    (px cp.vl ≤ px p ∧ px p < px cp.vl1) ∧
    (py cp.uk ≤ py p ∧ py p < py cp.uk1) ∧
    (py cp.vl1 ≤ py p ∧ py p < py cp.vl) := by
  have h := c.wx_mem_pivot cp
  simp only [Pivot, mem_filter, mem_univ, true_and] at h
  rw [mem_inter, mem_Ico, mem_Ico] at h
  rw [mem_inter, mem_Ico, mem_Ico] at h
  rcases h with ⟨⟨hx_u, hx_v⟩, ⟨hy_u, hy_v⟩⟩
  exact ⟨hx_u, hx_v, hy_u, hy_v⟩

lemma wx_not_black (cp : CrossingPoints c) : c.wx cp ∉ c.all_black :=
  c.pivot_no_black cp (c.wx cp) (c.wx_mem_pivot cp)

noncomputable def validLabels (cp : CrossingPoints c) : Finset (Label n) :=
  let to_W : Point n ↪ Label n := ⟨fun p => ⟨p, .W⟩, by intro a b h; injection h⟩
  let to_N : Point n ↪ Label n := ⟨fun p => ⟨p, .N⟩, by intro a b h; injection h⟩
  let to_E : Point n ↪ Label n := ⟨fun p => ⟨p, .E⟩, by intro a b h; injection h⟩
  let to_S : Point n ↪ Label n := ⟨fun p => ⟨p, .S⟩, by intro a b h; injection h⟩
  let to_X : Point n ↪ Label n := ⟨fun p => ⟨p, .X⟩, by intro a b h; injection h⟩

  (targetsWin c.u c.v c.all_black).map to_W ∪
  (targetsNin c.u c.v c.all_black).map to_N ∪
  (targetsEin c.u c.v c.all_black).map to_E ∪
  (targetsSin c.u c.v c.all_black).map to_S ∪
  map to_X {c.wx cp}

@[simp]
def covers (m : Matilda n c.all_black) (l : Label n) : Prop :=
  m.mem (label_pos l).2

lemma pivot_overlap_x (cp : CrossingPoints c) :
    px cp.vl < px cp.uk1 := by
  have h := c.wx_bounds cp
  linarith [h.1.2, h.2.1.1]

lemma u_y_le_uk_of_x_lt_uk1 (cp : CrossingPoints c) (q : Point n)
    (hq : q ∈ c.u) (hx : px q < px cp.uk1) : py q ≤ py cp.uk := by
  rw [← c.mem_u_list, List.mem_iff_get] at hq
  obtain ⟨i, rfl⟩ := hq
  have h_i_le_k : i.val ≤ cp.k.val := by
    by_contra h_gt
    push_neg at h_gt
    let k1_val := cp.k.val + 1
    have h_k1_valid : k1_val < c.u_list.length := by simp; omega
    let k1_idx : Fin c.u_list.length := ⟨k1_val, h_k1_valid⟩
    have h_idx_le : k1_idx ≤ i := by
      rw [Fin.le_iff_val_le_val]; exact h_gt
    have h_val_le : px (c.u_list.get k1_idx) ≤ px (c.u_list.get i) :=
      List.Pairwise.rel_get_of_le c.u_list_sorted h_idx_le
    have h_uk1_def : cp.uk1 = c.u_list.get k1_idx := by
      rw [cp.h_uk1]
    rw [← h_uk1_def] at h_val_le
    linarith
  let k_val := cp.k.val
  have h_k_valid : k_val < c.u_list.length := by simp; omega
  let k_idx : Fin c.u_list.length := ⟨k_val, h_k_valid⟩
  have h_idx_le : i ≤ k_idx := by
    rw [Fin.le_iff_val_le_val]; exact h_i_le_k
  have h_px_le : px (c.u_list.get i) ≤ px (c.u_list.get k_idx) :=
    List.Pairwise.rel_get_of_le c.u_list_sorted h_idx_le
  have h_uk_def : cp.uk = c.u_list.get k_idx := by
    rw [cp.h_uk]
  have mem_uk : cp.uk ∈ c.u := by
    rw [h_uk_def, ← c.mem_u_list]; exact List.get_mem c.u_list k_idx
  have mem_ui : c.u_list.get i ∈ c.u := by
    rw [← c.mem_u_list]; exact List.get_mem c.u_list i
  have h_px_le' : px (c.u_list.get i) ≤ px cp.uk := by
    rw [h_uk_def]; exact h_px_le
  apply c.u_mono_le (c.u_list.get i) mem_ui cp.uk mem_uk h_px_le'

lemma v_y_le_vl1_of_x_ge_uk1 (cp : CrossingPoints c) (q : Point n)
    (hq : q ∈ c.v) (hx : px cp.uk1 ≤ px q) : py q ≤ py cp.vl1 := by
  have h_vl_lt_q : px cp.vl < px q := lt_of_lt_of_le (c.pivot_overlap_x cp) hx
  rw [← c.mem_v_list, List.mem_iff_get] at hq
  obtain ⟨j, rfl⟩ := hq
  have h_idx_ge : cp.l.val + 1 ≤ j.val := by
    by_contra h_lt
    push_neg at h_lt
    let l_val := cp.l.val
    have h_l_valid : l_val < c.v_list.length := by simp; omega
    let l_idx : Fin c.v_list.length := ⟨l_val, h_l_valid⟩
    have h_idx_le : j ≤ l_idx := by
      rw [Fin.le_iff_val_le_val]; linarith
    have h_val_le : px (c.v_list.get j) ≤ px (c.v_list.get l_idx) :=
      List.Pairwise.rel_get_of_le c.v_list_sorted h_idx_le
    have h_vl_def : cp.vl = c.v_list.get l_idx := by
      rw [cp.h_vl]
    rw [← h_vl_def] at h_val_le
    linarith
  let l1_val := cp.l.val + 1
  have h_l1_valid : l1_val < c.v_list.length := by simp; omega
  let l1_idx : Fin c.v_list.length := ⟨l1_val, h_l1_valid⟩
  have h_idx_ge_fin : l1_idx ≤ j := by
    rw [Fin.le_iff_val_le_val]; exact h_idx_ge
  have h_px_le : px (c.v_list.get l1_idx) ≤ px (c.v_list.get j) :=
    List.Pairwise.rel_get_of_le c.v_list_sorted h_idx_ge_fin
  have h_vl1_def : cp.vl1 = c.v_list.get l1_idx := by
    rw [cp.h_vl1]
  have mem_vl1 : cp.vl1 ∈ c.v := by
    rw [h_vl1_def, ← c.mem_v_list]; exact List.get_mem _ _
  have mem_vl1 : cp.vl1 ∈ c.v := by
    rw [h_vl1_def, ← c.mem_v_list]; exact List.get_mem c.v_list l1_idx
  have mem_vj : c.v_list.get j ∈ c.v := by
    rw [← c.mem_v_list]; exact List.get_mem c.v_list j
  have h_px_le' : px cp.vl1 ≤ px (c.v_list.get j) := by
    rw [h_vl1_def]; exact h_px_le
  apply c.v_mono_le cp.vl1 mem_vl1 (c.v_list.get j) mem_vj h_px_le'

lemma disjoint_label_X_W (cp : CrossingPoints c) (m : Matilda n c.all_black) (bw : Point n)
    (hbw : bw ∈ c.all_black) (hbw_pos : 0 < py bw)
    (h_w_in : m.mem ⟨bw.1, bw.2 - 1⟩)
    (h_x_in : m.mem (c.wx cp))
    (h_bw_reg : bw ∈ regionWExtend c.u c.v) : False := by
  obtain ⟨hx_u, hx_v, hy_u, hy_v⟩ := c.wx_bounds cp
  let wx := c.wx cp
  simp only [Matilda.mem, px_mk_val, py_mk_val] at h_w_in h_x_in
  have h_w_sub : ↑(bw.2 - 1).val = py bw - 1 := fin_val_sub_one_eq hbw_pos
  rw [mem_regionWExtend] at h_bw_reg
  obtain ⟨h_bw_u_lo, h_bw_v_lo⟩ := h_bw_reg
  have h_py_le : py bw ≤ py wx := by
    by_cases h_split : px bw < px cp.uk1
    · rw [mem_u_lower] at h_bw_u_lo
      obtain ⟨ui, hui, hx_le, hy_ge⟩ := h_bw_u_lo
      have h_ui_lt : px ui < px cp.uk1 := lt_of_le_of_lt hx_le h_split
      have h_y_bound : py ui ≤ py cp.uk := c.u_y_le_uk_of_x_lt_uk1 cp ui hui h_ui_lt
      linarith [hy_ge, hy_u.1]
    · push_neg at h_split
      rw [mem_v_lower] at h_bw_v_lo
      obtain ⟨vj, hvj, hx_le, hy_ge⟩ := h_bw_v_lo
      have h_vj_ge : px cp.uk1 ≤ px vj := le_trans h_split hx_le
      have h_y_bound : py vj ≤ py cp.vl1 := c.v_y_le_vl1_of_x_ge_uk1 cp vj hvj h_vj_ge
      linarith [hy_ge, hy_v.1]
  have h_bw_in_m : m.mem bw := by
    simp only [Matilda.mem]
    repeat (first | constructor | linarith | omega)
  exact m.h_disjoint bw hbw h_bw_in_m

lemma u_x_le_uk_of_y_lt_uk1 (cp : CrossingPoints c) (q : Point n)
    (hq : q ∈ c.u) (hy : py q < py cp.uk1) : px q ≤ px cp.uk := by
  rw [← c.mem_u_list, List.mem_iff_get] at hq
  obtain ⟨i, rfl⟩ := hq
  have h_idx_le : i.val ≤ cp.k.val := by
    by_contra h_gt; push_neg at h_gt
    let k1_idx : Fin c.u_list.length := ⟨cp.k.val + 1, by simp; omega⟩
    have h_idx_le : k1_idx ≤ i := by rw [Fin.le_iff_val_le_val]; exact h_gt
    have h_x_le : px (c.u_list.get k1_idx) ≤ px (c.u_list.get i) :=
      List.Pairwise.rel_get_of_le c.u_list_sorted h_idx_le
    have h_uk1_def : cp.uk1 = c.u_list.get k1_idx := by rw [cp.h_uk1]
    have mem_uk1 : cp.uk1 ∈ c.u := by rw [h_uk1_def, ← c.mem_u_list]; exact List.get_mem _ _
    have mem_ui : c.u_list.get i ∈ c.u := by
      rw [← c.mem_u_list]; exact List.get_mem c.u_list i
    have : py cp.uk1 ≤ py (c.u_list.get i) := by
      rw [← h_uk1_def] at h_x_le
      apply c.u_mono_le cp.uk1 mem_uk1 (c.u_list.get i) mem_ui h_x_le
    linarith
  let k_idx : Fin c.u_list.length := ⟨cp.k.val, by rw [c.u_list_length]; have := cp.k.isLt; omega⟩
  have h_idx_le_k : i ≤ k_idx := by rw [Fin.le_iff_val_le_val]; exact h_idx_le
  have : px (c.u_list.get i) ≤ px (c.u_list.get k_idx) :=
    List.Pairwise.rel_get_of_le c.u_list_sorted h_idx_le_k
  rwa [← cp.h_uk] at this

lemma pivot_overlap_y (cp : CrossingPoints c) :
    py cp.vl1 < py cp.uk1 := by
  have h := c.wx_bounds cp
  linarith [h.1, h.2]

lemma v_x_le_vl_of_y_ge_uk1 (cp : CrossingPoints c) (q : Point n)
    (hq : q ∈ c.v) (hy : py cp.uk1 ≤ py q) : px q ≤ px cp.vl := by
  rw [← c.mem_v_list, List.mem_iff_get] at hq
  obtain ⟨j, rfl⟩ := hq
  by_contra h_gt
  push_neg at h_gt
  have h_l_lt_j : cp.l.val < j.val := by
    by_contra h_le
    push_neg at h_le
    let l_idx : Fin c.v_list.length := ⟨cp.l.val, by rw [c.v_list_length]; have := cp.l.isLt; omega⟩
    have h_idx_le : j ≤ l_idx := by rw [Fin.le_iff_val_le_val]; exact h_le
    have h_x_le : px (c.v_list.get j) ≤ px (c.v_list.get l_idx) :=
      List.Pairwise.rel_get_of_le c.v_list_sorted h_idx_le
    have h_vl_def : cp.vl = c.v_list.get l_idx := by rw [cp.h_vl]
    rw [← h_vl_def] at h_x_le
    linarith
  let l1_idx : Fin c.v_list.length := ⟨cp.l.val + 1, by simp; omega⟩
  have h_idx_ge : l1_idx ≤ j := by rw [Fin.le_iff_val_le_val]; exact h_l_lt_j
  have h_x_ge : px (c.v_list.get l1_idx) ≤ px (c.v_list.get j) :=
    List.Pairwise.rel_get_of_le c.v_list_sorted h_idx_ge
  have h_vl1_def : cp.vl1 = c.v_list.get l1_idx := by rw [cp.h_vl1]
  have mem_vl1 : cp.vl1 ∈ c.v := by
    rw [h_vl1_def, ← c.mem_v_list]; exact List.get_mem c.v_list l1_idx
  have mem_q : c.v_list.get j ∈ c.v := by
    rw [← c.mem_v_list]; exact List.get_mem c.v_list j
  have h_y_le : py (c.v_list.get j) ≤ py cp.vl1 := by
    rw [← h_vl1_def] at h_x_ge
    apply c.v_mono_le cp.vl1 mem_vl1 (c.v_list.get j) mem_q h_x_ge
  have h_pivot_y := c.pivot_overlap_y cp
  linarith

lemma disjoint_label_X_N (cp : CrossingPoints c) (m : Matilda n c.all_black) (bn : Point n)
    (hbn : bn ∈ c.all_black) (hbn_pos : 0 < px bn)
    (h_n_in : m.mem ⟨bn.1 - 1, bn.2⟩)
    (h_x_in : m.mem (c.wx cp))
    (h_bn_reg : bn ∈ regionNExtend c.u c.v) : False := by
  obtain ⟨hx_u, hx_v, hy_u, hy_v⟩ := c.wx_bounds cp
  let wx := c.wx cp
  simp only [Matilda.mem, px_mk_val, py_mk_val] at h_n_in h_x_in
  have h_n_sub : ↑(bn.1 - 1).val = px bn - 1 := fin_val_sub_one_eq hbn_pos
  rw [mem_regionNExtend] at h_bn_reg
  obtain ⟨h_bn_u_up, h_bn_v_lo⟩ := h_bn_reg
  have h_px_le : px bn ≤ px wx := by
    by_cases h_split : py bn < py cp.uk1
    · rw [mem_u_upper] at h_bn_u_up
      obtain ⟨ui, hui, hx_le, hy_le⟩ := h_bn_u_up
      have h_ui_lt : py ui < py cp.uk1 := lt_of_le_of_lt hy_le h_split
      have h_x_bound : px ui ≤ px cp.uk := c.u_x_le_uk_of_y_lt_uk1 cp ui hui h_ui_lt
      linarith [hx_le, hx_u.1]
    · push_neg at h_split
      rw [mem_v_lower] at h_bn_v_lo
      obtain ⟨vj, hvj, hx_le, hy_le⟩ := h_bn_v_lo
      have h_vj_ge : py cp.uk1 ≤ py vj := le_trans h_split hy_le
      have h_x_bound : px vj ≤ px cp.vl := c.v_x_le_vl_of_y_ge_uk1 cp vj hvj h_vj_ge
      linarith [hx_le, hx_v.1]
  have h_bn_in_m : m.mem bn := by
    simp only [Matilda.mem]
    repeat (first | constructor | linarith | omega)
  exact m.h_disjoint bn hbn h_bn_in_m

lemma u_x_ge_uk1_of_x_gt_uk (cp : CrossingPoints c) (q : Point n)
    (hq : q ∈ c.u) (hx : px cp.uk < px q) : px cp.uk1 ≤ px q := by
  rw [← c.mem_u_list, List.mem_iff_get] at hq
  obtain ⟨i, rfl⟩ := hq
  by_contra h_lt
  have h_idx_gt : cp.k.val < i.val := by
    by_contra h_le; push_neg at h_le
    let k_idx : Fin c.u_list.length := ⟨cp.k.val, by simp; omega⟩
    have h_idx_le : i ≤ k_idx := by rw [Fin.le_iff_val_le_val]; exact h_le
    have h_val_le : px (c.u_list.get i) ≤ px (c.u_list.get k_idx) :=
      List.Pairwise.rel_get_of_le c.u_list_sorted h_idx_le
    have h_uk_def : cp.uk = c.u_list.get k_idx := by rw [cp.h_uk]
    rw [← h_uk_def] at h_val_le
    linarith
  have h_idx_lt : i.val < cp.k.val + 1 := by
    by_contra h_ge; push_neg at h_ge
    let k1_idx : Fin c.u_list.length := ⟨cp.k.val + 1, by simp; omega⟩
    have h_idx_ge : k1_idx ≤ i := by rw [Fin.le_iff_val_le_val]; exact h_ge
    have h_val_ge : px (c.u_list.get k1_idx) ≤ px (c.u_list.get i) :=
      List.Pairwise.rel_get_of_le c.u_list_sorted h_idx_ge
    have h_uk1_def : cp.uk1 = c.u_list.get k1_idx := by rw [cp.h_uk1]
    rw [← h_uk1_def] at h_val_ge
    linarith
  omega

lemma disjoint_label_X_E (cp : CrossingPoints c) (m : Matilda n c.all_black) (be : Point n)
    (hbe : be ∈ c.all_black) (hbe_bound : py be < n - 1)
    (h_x_in : m.mem (c.wx cp))
    (h_e_in : m.mem ⟨be.1, be.2 + 1⟩)
    (h_be_reg : be ∈ regionEExtend c.u c.v) : False := by
  obtain ⟨hx_u, hx_v, hy_u, hy_v⟩ := c.wx_bounds cp
  let wx := c.wx cp
  simp only [Matilda.mem, px_mk_val, py_mk_val] at h_e_in h_x_in
  have h_e_add : ↑(be.2 + 1).val = py be + 1 := fin_val_add_one_eq hbe_bound
  rw [mem_regionEExtend] at h_be_reg
  obtain ⟨h_be_u_up, h_be_v_up⟩ := h_be_reg
  have h_py_le : py wx ≤ py be := by
    by_cases h_split_u : px cp.uk1 ≤ px be
    · rw [mem_u_upper] at h_be_u_up
      obtain ⟨qi, hqi, hx_le, hy_le⟩ := h_be_u_up
      have h_idx_le : px cp.uk1 ≤ px qi := le_trans h_split_u hx_le
      have h_uk1_mem : cp.uk1 ∈ c.u := by
        rw [cp.h_uk1, ← c.mem_u_list]; exact List.get_mem _ _
      have h_y_le : py cp.uk1 ≤ py qi :=
        c.u_mono_le cp.uk1 h_uk1_mem qi hqi h_idx_le
      linarith [hy_u.2, hy_le]
    · push_neg at h_split_u
      by_cases h_split_v : px be < px cp.vl1
      · rw [mem_v_upper] at h_be_v_up
        obtain ⟨rj, hrj, hx_le, hy_le⟩ := h_be_v_up
        have h_idx_lt : px rj < px cp.vl1 := lt_of_le_of_lt hx_le h_split_v
        rw [← c.mem_v_list, List.mem_iff_get] at hrj
        obtain ⟨j, rfl⟩ := hrj
        have h_j_le_l : j.val ≤ cp.l.val := by
          by_contra h_gt; push_neg at h_gt
          let l1_idx : Fin c.v_list.length := ⟨cp.l.val + 1, by simp; omega⟩
          have h_idx_le : l1_idx ≤ j := by rw [Fin.le_iff_val_le_val]; exact h_gt
          have h_val_le : px (c.v_list.get l1_idx) ≤ px (c.v_list.get j) :=
             List.Pairwise.rel_get_of_le c.v_list_sorted h_idx_le
          have h_vl1_def : cp.vl1 = c.v_list.get l1_idx := by rw [cp.h_vl1]
          rw [← h_vl1_def] at h_val_le
          linarith
        let l_idx : Fin c.v_list.length := ⟨cp.l.val, by simp; omega⟩
        have h_idx_le : j ≤ l_idx := by rw [Fin.le_iff_val_le_val]; exact h_j_le_l
        have h_x_le_vl : px (c.v_list.get j) ≤ px (c.v_list.get l_idx) :=
          List.Pairwise.rel_get_of_le c.v_list_sorted h_idx_le
        have h_vl_def : cp.vl = c.v_list.get l_idx := by rw [cp.h_vl]
        have mem_vl : cp.vl ∈ c.v := by rw [h_vl_def, ← c.mem_v_list]; exact List.get_mem _ _
        have mem_rj : c.v_list.get j ∈ c.v := by rw [← c.mem_v_list]; exact List.get_mem _ _
        rw [← h_vl_def] at h_x_le_vl
        have h_y_ge_vl : py cp.vl ≤ py (c.v_list.get j) :=
          c.v_mono_le (c.v_list.get j) mem_rj cp.vl mem_vl h_x_le_vl
        linarith [hy_v.2, hy_le]
      · push_neg at h_split_v
        rw [mem_u_upper] at h_be_u_up
        obtain ⟨qi, hqi, hx_le, hy_le⟩ := h_be_u_up
        have h_uk_lt_qi : px cp.uk < px qi := by
           have h_uk_lt_vl1 : px cp.uk < px cp.vl1 := by
             have h := c.wx_bounds cp
             linarith [h.1, h.2]
           linarith
        have h_uk1_le_qi : px cp.uk1 ≤ px qi :=
          c.u_x_ge_uk1_of_x_gt_uk cp qi hqi h_uk_lt_qi
        have h_uk1_mem : cp.uk1 ∈ c.u := by
          rw [cp.h_uk1, ← c.mem_u_list]; exact List.get_mem _ _
        have h_y_ge_uk1 : py cp.uk1 ≤ py qi :=
          c.u_mono_le cp.uk1 h_uk1_mem qi hqi h_uk1_le_qi
        linarith [hy_u.2, hy_le]
  have h_be_in_m : m.mem be := by
    simp only [Matilda.mem]
    repeat (first | constructor | linarith | omega)
  exact m.h_disjoint be hbe h_be_in_m

lemma pivot_overlap_y_2 (cp : CrossingPoints c) :
    py cp.uk < py cp.vl := by
  have h := c.wx_bounds cp
  linarith [h.2]

lemma v_y_ge_vl_of_x_lt_vl1 (cp : CrossingPoints c) (q : Point n)
    (hq : q ∈ c.v) (hx : px q < px cp.vl1) : py cp.vl ≤ py q := by
  rw [← c.mem_v_list, List.mem_iff_get] at hq
  obtain ⟨j, rfl⟩ := hq
  have h_idx_le : j.val ≤ cp.l.val := by
    by_contra h_gt; push_neg at h_gt
    let l1_idx : Fin c.v_list.length := ⟨cp.l.val + 1, by simp; omega⟩
    have h_idx_le : l1_idx ≤ j := by rw [Fin.le_iff_val_le_val]; exact h_gt
    have h_x_le : px (c.v_list.get l1_idx) ≤ px (c.v_list.get j) :=
      List.Pairwise.rel_get_of_le c.v_list_sorted h_idx_le
    have h_vl1_def : cp.vl1 = c.v_list.get l1_idx := by rw [cp.h_vl1]
    rw [← h_vl1_def] at h_x_le
    linarith
  let l_idx : Fin c.v_list.length := ⟨cp.l.val, by simp; omega⟩
  have h_idx_le_fin : j ≤ l_idx := by rw [Fin.le_iff_val_le_val]; exact h_idx_le
  have h_x_le : px (c.v_list.get j) ≤ px (c.v_list.get l_idx) :=
     List.Pairwise.rel_get_of_le c.v_list_sorted h_idx_le_fin
  have h_vl_def : cp.vl = c.v_list.get l_idx := by rw [cp.h_vl]
  have mem_vl : cp.vl ∈ c.v := by rw [h_vl_def, ← c.mem_v_list]; exact List.get_mem _ _
  have mem_q : c.v_list.get j ∈ c.v := by rw [← c.mem_v_list]; exact List.get_mem _ _
  rw [← h_vl_def] at h_x_le
  apply c.v_mono_le _ mem_q _ mem_vl h_x_le

lemma u_x_ge_uk1_of_y_ge_vl (cp : CrossingPoints c) (q : Point n)
    (hq : q ∈ c.u) (hy : py cp.vl ≤ py q) : px cp.uk1 ≤ px q := by
  have h_pivot := c.pivot_overlap_y_2 cp
  have h_uk_lt_q : py cp.uk < py q := lt_of_lt_of_le h_pivot hy
  rw [← c.mem_u_list, List.mem_iff_get] at hq
  obtain ⟨i, rfl⟩ := hq
  have h_idx_ge : cp.k.val + 1 ≤ i.val := by
    by_contra h_lt; push_neg at h_lt
    let k_idx : Fin c.u_list.length := ⟨cp.k.val, by rw [c.u_list_length]; have := cp.k.isLt; omega⟩
    have h_idx_le : i ≤ k_idx := by rw [Fin.le_iff_val_le_val]; linarith
    have h_x_le : px (c.u_list.get i) ≤ px (c.u_list.get k_idx) :=
      List.Pairwise.rel_get_of_le c.u_list_sorted h_idx_le
    have h_uk_def : cp.uk = c.u_list.get k_idx := by rw [cp.h_uk]
    have mem_uk : cp.uk ∈ c.u := by rw [h_uk_def, ← c.mem_u_list]; exact List.get_mem _ _
    have mem_q : c.u_list.get i ∈ c.u := by rw [← c.mem_u_list]; exact List.get_mem _ _
    rw [← h_uk_def] at h_x_le
    have h_y_le : py (c.u_list.get i) ≤ py cp.uk :=
      c.u_mono_le _ mem_q _ mem_uk h_x_le
    linarith
  let k1_idx : Fin c.u_list.length := ⟨cp.k.val + 1, by simp; omega⟩
  have h_idx_ge_fin : k1_idx ≤ i := by rw [Fin.le_iff_val_le_val]; exact h_idx_ge
  have h_x_ge : px (c.u_list.get k1_idx) ≤ px (c.u_list.get i) :=
    List.Pairwise.rel_get_of_le c.u_list_sorted h_idx_ge_fin
  have h_uk1_def : cp.uk1 = c.u_list.get k1_idx := by rw [cp.h_uk1]
  rw [← h_uk1_def] at h_x_ge
  exact h_x_ge

lemma disjoint_label_X_S (cp : CrossingPoints c) (m : Matilda n c.all_black) (bs : Point n)
    (hbs : bs ∈ c.all_black) (hbs_bound : px bs < n - 1)
    (h_s_in : m.mem ⟨bs.1 + 1, bs.2⟩)
    (h_x_in : m.mem (c.wx cp))
    (h_bs_reg : bs ∈ regionSExtend c.u c.v) : False := by
  obtain ⟨hx_u, hx_v, hy_u, hy_v⟩ := c.wx_bounds cp
  let wx := c.wx cp
  simp only [Matilda.mem, px_mk_val, py_mk_val] at h_s_in h_x_in
  have h_s_add : ↑(bs.1 + 1).val = px bs + 1 := fin_val_add_one_eq hbs_bound
  rw [mem_regionSExtend] at h_bs_reg
  obtain ⟨h_bs_u_lo, h_bs_v_up⟩ := h_bs_reg
  have h_px_le : px wx ≤ px bs := by
    by_cases h_split : px bs < px cp.vl1
    · rw [mem_v_upper] at h_bs_v_up
      obtain ⟨vj, hvj, hx_le, hy_le⟩ := h_bs_v_up
      have h_vj_lt_vl1 : px vj < px cp.vl1 := lt_of_le_of_lt hx_le h_split
      have h_y_ge_vl : py cp.vl ≤ py vj := c.v_y_ge_vl_of_x_lt_vl1 cp vj hvj h_vj_lt_vl1
      have h_bs_y_ge : py cp.vl ≤ py bs := le_trans h_y_ge_vl hy_le
      rw [mem_u_lower] at h_bs_u_lo
      obtain ⟨ui, hui, h_ui_x_le, h_ui_y_ge⟩ := h_bs_u_lo
      have h_ui_y_ge : py cp.vl ≤ py ui := le_trans h_bs_y_ge h_ui_y_ge
      have h_ui_x_ge : px cp.uk1 ≤ px ui := c.u_x_ge_uk1_of_y_ge_vl cp ui hui h_ui_y_ge
      linarith [hx_u.2, h_ui_x_le]
    · push_neg at h_split
      linarith [hx_v.2]
  have h_bs_in_m : m.mem bs := by
    simp only [Matilda.mem]
    repeat (first | constructor | linarith | omega)
  exact m.h_disjoint bs hbs h_bs_in_m

open Classical

lemma matilda_covers_at_most_one (cp : CrossingPoints c) (m : Matilda n c.all_black) :
    ({l ∈ validLabels c cp | covers c m l}).card ≤ 1 := by
  rw [card_le_one_iff]
  intro l1 l2 hl1 hl2
  rw [mem_filter] at hl1 hl2
  obtain ⟨h_valid1, h_cov1⟩ := hl1
  obtain ⟨h_valid2, h_cov2⟩ := hl2
  by_contra h_ne

  let p1 := l1.source; let t1 := l1.type; let p2 := l2.source; let t2 := l2.type
  have get_props : ∀ l ∈ validLabels c cp,
      (l.type = .W → l.source ∈ targetsWin c.u c.v c.all_black) ∧
      (l.type = .N → l.source ∈ targetsNin c.u c.v c.all_black) ∧
      (l.type = .E → l.source ∈ targetsEin c.u c.v c.all_black) ∧
      (l.type = .S → l.source ∈ targetsSin c.u c.v c.all_black) ∧
      (l.type = .X → l.source = c.wx cp) := by
    intros l hl
    simp only [validLabels, mem_union, mem_map, or_assoc] at hl
    rcases hl with ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩
    <;> simp_all [mem_singleton]

  have props1 := get_props l1 h_valid1; have props2 := get_props l2 h_valid2
  cases h1 : l1.type <;> cases h2 : l2.type
  · have hp1 := props1.1 h1; have hp2 := props2.1 h2
    simp only [mem_targetsWin, mem_targetsW] at hp1 hp2
    simp [h1, h2] at h_cov1 h_cov2
    have h_p_ne : p1 ≠ p2 := by
      contrapose! h_ne
      rcases l1 with ⟨src1, type1⟩
      rcases l2 with ⟨src2, type2⟩
      simp only [Label.mk.injEq]
      constructor
      · exact h_ne
      · simp at h1 h2; rw [h1, h2]
    exact unique_label_W (m := m) (p := p1) (q := p2)
      (hp := hp1.1.1) (hq := hp2.1.1) (h_ne := h_p_ne)
      (hp_pos := hp1.2) (hq_pos := hp2.2)
      (hp_in := h_cov1) (hq_in := h_cov2) (h_unique_y := c.h_unique_y)
  · have hW := props1.1 h1; have hN := props2.2.1 h2
    simp only [mem_targetsWin, mem_targetsW] at hW
    simp only [mem_targetsNin, mem_targetsN] at hN
    simp [h1, h2] at h_cov1 h_cov2
    apply disjoint_label_W_N (m := m) (u := c.u) (bw := p1) (bn := p2)
      (hbw := hW.1.1) (hbn := hN.1.1) (hbw_pos := hW.2) (hbn_pos := hN.2)
      (h_u_mono := c.u_mono_le) (h_u_inj := c.u_inj_y)
      (h_w_in := h_cov1) (h_n_in := h_cov2)
    · simp only [mem_regionWExtend] at hW; exact hW.1.2.1
    · simp only [mem_regionNExtend] at hN; exact hN.1.2.1
  · have hW := props1.1 h1; have hE := props2.2.2.1 h2
    simp only [mem_targetsWin, mem_targetsW] at hW
    simp only [mem_targetsEin, mem_targetsE] at hE
    simp [h1, h2] at h_cov1 h_cov2
    apply disjoint_label_W_E (m := m) (u := c.u) (v := c.v) (bw := p1) (be := p2)
      (hbw := hW.1.1) (hbw_pos := hW.2) (hbe_bound := hE.2)
      (h_u_mono := c.u_mono_le) (h_v_mono := c.v_mono_le) (h_u_inj := c.u_inj_y)
      (h_w_in := h_cov1) (h_e_in := h_cov2)
      (h_bw_reg := hW.1.2) (h_be_reg := hE.1.2)
  · have hW := props1.1 h1; have hS := props2.2.2.2.1 h2
    simp only [mem_targetsWin, mem_targetsW] at hW
    simp only [mem_targetsSin, mem_targetsS] at hS
    simp [h1, h2] at h_cov1 h_cov2
    apply disjoint_label_S_W (m := m) (v := c.v) (bs := p2) (bw := p1)
      (hbs := hS.1.1) (hbw := hW.1.1) (hbs_bound := hS.2) (hbw_pos := hW.2)
      (h_v_mono := c.v_mono_le) (h_v_inj := c.v_inj_y)
      (h_s_in := h_cov2) (h_w_in := h_cov1)
    · simp only [mem_regionSExtend] at hS; exact hS.1.2.2
    · simp only [mem_regionWExtend] at hW; exact hW.1.2.2
  · have hW := props1.1 h1; have hX := props2.2.2.2.2 h2
    simp only [mem_targetsWin, mem_targetsW] at hW
    simp [h1, h2] at h_cov1 h_cov2
    rw [hX] at h_cov2
    apply disjoint_label_X_W (cp := cp) (m := m) (bw := p1)
      (hbw := hW.1.1) (hbw_pos := hW.2)
      (h_w_in := h_cov1) (h_x_in := h_cov2)
    · exact hW.1.2
  · have hN := props1.2.1 h1; have hW := props2.1 h2
    simp only [mem_targetsWin, mem_targetsW] at hW
    simp only [mem_targetsNin, mem_targetsN] at hN
    simp [h1, h2] at h_cov1 h_cov2
    apply disjoint_label_W_N (m := m) (u := c.u) (bw := p2) (bn := p1)
      (hbw := hW.1.1) (hbn := hN.1.1) (hbw_pos := hW.2) (hbn_pos := hN.2)
      (h_u_mono := c.u_mono_le) (h_u_inj := c.u_inj_y)
      (h_w_in := h_cov2) (h_n_in := h_cov1)
    · simp only [mem_regionWExtend] at hW; exact hW.1.2.1
    · simp only [mem_regionNExtend] at hN; exact hN.1.2.1
  · have hp1 := props1.2.1 h1; have hp2 := props2.2.1 h2
    simp only [mem_targetsNin, mem_targetsN] at hp1 hp2
    simp [h1, h2] at h_cov1 h_cov2
    have h_p_ne : p1 ≠ p2 := by
      contrapose! h_ne
      rcases l1 with ⟨src1, type1⟩
      rcases l2 with ⟨src2, type2⟩
      simp only [Label.mk.injEq]
      constructor
      · exact h_ne
      · simp at h1 h2; rw [h1, h2]
    exact unique_label_N (m := m) (p := p1) (q := p2)
      (hp := hp1.1.1) (hq := hp2.1.1) (h_ne := h_p_ne)
      (hp_pos := hp1.2) (hq_pos := hp2.2)
      (hp_in := h_cov1) (hq_in := h_cov2) (h_unique_x := c.h_unique_x)
  · have hN := props1.2.1 h1; have hE := props2.2.2.1 h2
    simp only [mem_targetsNin, mem_targetsN] at hN
    simp only [mem_targetsEin, mem_targetsE] at hE
    simp [h1, h2] at h_cov1 h_cov2
    apply disjoint_label_E_N (m := m) (v := c.v) (be := p2) (bn := p1)
      (hbe := hE.1.1) (hbn := hN.1.1) (hbe_bound := hE.2) (hbn_pos := hN.2)
      (h_v_mono := c.v_mono_le) (h_v_inj := c.v_inj_y)
      (h_e_in := h_cov2) (h_n_in := h_cov1)
    · simp only [mem_regionEExtend] at hE; exact hE.1.2.2
    · simp only [mem_regionNExtend] at hN; exact hN.1.2.2
  · have hN := props1.2.1 h1; have hS := props2.2.2.2.1 h2
    simp only [mem_targetsNin, mem_targetsN] at hN
    simp only [mem_targetsSin, mem_targetsS] at hS
    simp [h1, h2] at h_cov1 h_cov2
    apply disjoint_label_N_S (m := m) (u := c.u) (v := c.v) (bn := p1) (bs := p2)
      (hbn := hN.1.1) (hbn_pos := hN.2) (hbs_bound := hS.2)
      (h_u_mono := c.u_mono_le) (h_v_mono := c.v_mono_le) (h_v_inj := c.v_inj_y)
      (h_n_in := h_cov1) (h_s_in := h_cov2)
      (h_bn_reg := hN.1.2) (h_bs_reg := hS.1.2)
  · have hN := props1.2.1 h1; have hX := props2.2.2.2.2 h2
    simp only [mem_targetsNin, mem_targetsN] at hN
    simp [h1, h2] at h_cov1 h_cov2
    rw [hX] at h_cov2
    apply disjoint_label_X_N (cp := cp) (m := m) (bn := p1)
      (hbn := hN.1.1) (hbn_pos := hN.2)
      (h_n_in := h_cov1) (h_x_in := h_cov2)
    · exact hN.1.2
  · have hE := props1.2.2.1 h1; have hW := props2.1 h2
    simp only [mem_targetsEin, mem_targetsE] at hE
    simp only [mem_targetsWin, mem_targetsW] at hW
    simp [h1, h2] at h_cov1 h_cov2
    apply disjoint_label_W_E (m := m) (u := c.u) (v := c.v) (bw := p2) (be := p1)
      (hbw := hW.1.1) (hbw_pos := hW.2) (hbe_bound := hE.2)
      (h_u_mono := c.u_mono_le) (h_v_mono := c.v_mono_le) (h_u_inj := c.u_inj_y)
      (h_w_in := h_cov2) (h_e_in := h_cov1)
      (h_bw_reg := hW.1.2) (h_be_reg := hE.1.2)
  · have hE := props1.2.2.1 h1; have hN := props2.2.1 h2
    simp only [mem_targetsEin, mem_targetsE] at hE
    simp only [mem_targetsNin, mem_targetsN] at hN
    simp [h1, h2] at h_cov1 h_cov2
    apply disjoint_label_E_N (m := m) (v := c.v) (be := p1) (bn := p2)
      (hbe := hE.1.1) (hbn := hN.1.1) (hbe_bound := hE.2) (hbn_pos := hN.2)
      (h_v_mono := c.v_mono_le) (h_v_inj := c.v_inj_y)
      (h_e_in := h_cov1) (h_n_in := h_cov2)
    · simp only [mem_regionEExtend] at hE; exact hE.1.2.2
    · simp only [mem_regionNExtend] at hN; exact hN.1.2.2
  · have hp1 := props1.2.2.1 h1; have hp2 := props2.2.2.1 h2
    simp only [mem_targetsEin, mem_targetsE] at hp1 hp2
    simp [h1, h2] at h_cov1 h_cov2
    have h_p_ne : p1 ≠ p2 := by
      contrapose! h_ne
      rcases l1 with ⟨src1, type1⟩
      rcases l2 with ⟨src2, type2⟩
      simp only [Label.mk.injEq]
      constructor
      · exact h_ne
      · simp at h1 h2; rw [h1, h2]
    exact unique_label_E (m := m) (p := p1) (q := p2)
      (hp := hp1.1.1) (hq := hp2.1.1) (h_ne := h_p_ne)
      (hp_bound := hp1.2) (hq_bound := hp2.2)
      (hp_in := h_cov1) (hq_in := h_cov2) (h_unique_y := c.h_unique_y)
  · have hE := props1.2.2.1 h1; have hS := props2.2.2.2.1 h2
    simp only [mem_targetsEin, mem_targetsE] at hE
    simp only [mem_targetsSin, mem_targetsS] at hS
    simp [h1, h2] at h_cov1 h_cov2
    apply disjoint_label_E_S (m := m) (u := c.u) (be := p1) (bs := p2)
      (hbe := hE.1.1) (hbs := hS.1.1) (hbe_bound := hE.2) (hbs_bound := hS.2)
      (h_u_mono := c.u_mono_le) (h_u_inj := c.u_inj_y)
      (h_e_in := h_cov1) (h_s_in := h_cov2)
    · simp only [mem_regionEExtend] at hE; exact hE.1.2.1
    · simp only [mem_regionSExtend] at hS; exact hS.1.2.1
  · have hE := props1.2.2.1 h1; have hX := props2.2.2.2.2 h2
    simp only [mem_targetsEin, mem_targetsE] at hE
    simp [h1, h2] at h_cov1 h_cov2
    rw [hX] at h_cov2
    apply disjoint_label_X_E (cp := cp) (m := m) (be := p1)
      (hbe := hE.1.1) (hbe_bound := hE.2)
      (h_x_in := h_cov2) (h_e_in := h_cov1)
    · exact hE.1.2
  · have hS := props1.2.2.2.1 h1; have hW := props2.1 h2
    simp only [mem_targetsSin, mem_targetsS] at hS
    simp only [mem_targetsWin, mem_targetsW] at hW
    simp [h1, h2] at h_cov1 h_cov2
    apply disjoint_label_S_W (m := m) (v := c.v) (bs := p1) (bw := p2)
      (hbs := hS.1.1) (hbw := hW.1.1) (hbs_bound := hS.2) (hbw_pos := hW.2)
      (h_v_mono := c.v_mono_le) (h_v_inj := c.v_inj_y)
      (h_s_in := h_cov1) (h_w_in := h_cov2)
    · simp only [mem_regionSExtend] at hS; exact hS.1.2.2
    · simp only [mem_regionWExtend] at hW; exact hW.1.2.2
  · have hS := props1.2.2.2.1 h1; have hN := props2.2.1 h2
    simp only [mem_targetsSin, mem_targetsS] at hS
    simp only [mem_targetsNin, mem_targetsN] at hN
    simp [h1, h2] at h_cov1 h_cov2
    apply disjoint_label_N_S (m := m) (u := c.u) (v := c.v) (bn := p2) (bs := p1)
      (hbn := hN.1.1) (hbn_pos := hN.2) (hbs_bound := hS.2)
      (h_u_mono := c.u_mono_le) (h_v_mono := c.v_mono_le) (h_v_inj := c.v_inj_y)
      (h_n_in := h_cov2) (h_s_in := h_cov1)
      (h_bn_reg := hN.1.2) (h_bs_reg := hS.1.2)
  · have hS := props1.2.2.2.1 h1; have hE := props2.2.2.1 h2
    simp only [mem_targetsSin, mem_targetsS] at hS
    simp only [mem_targetsEin, mem_targetsE] at hE
    simp [h1, h2] at h_cov1 h_cov2
    apply disjoint_label_E_S (m := m) (u := c.u) (be := p2) (bs := p1)
      (hbe := hE.1.1) (hbs := hS.1.1) (hbe_bound := hE.2) (hbs_bound := hS.2)
      (h_u_mono := c.u_mono_le) (h_u_inj := c.u_inj_y)
      (h_e_in := h_cov2) (h_s_in := h_cov1)
    · simp only [mem_regionEExtend] at hE; exact hE.1.2.1
    · simp only [mem_regionSExtend] at hS; exact hS.1.2.1
  · have hp1 := props1.2.2.2.1 h1; have hp2 := props2.2.2.2.1 h2
    simp only [mem_targetsSin, mem_targetsS] at hp1 hp2
    simp [h1, h2] at h_cov1 h_cov2
    have h_p_ne : p1 ≠ p2 := by
      contrapose! h_ne
      rcases l1 with ⟨src1, type1⟩
      rcases l2 with ⟨src2, type2⟩
      simp only [Label.mk.injEq]
      constructor
      · exact h_ne
      · simp at h1 h2; rw [h1, h2]
    exact unique_label_S (m := m) (p := p1) (q := p2)
      (hp := hp1.1.1) (hq := hp2.1.1) (h_ne := h_p_ne)
      (hp_bound := hp1.2) (hq_bound := hp2.2)
      (hp_in := h_cov1) (hq_in := h_cov2) (h_unique_x := c.h_unique_x)
  · have hS := props1.2.2.2.1 h1; have hX := props2.2.2.2.2 h2
    simp only [mem_targetsSin, mem_targetsS] at hS
    simp [h1, h2] at h_cov1 h_cov2
    rw [hX] at h_cov2
    apply disjoint_label_X_S (cp := cp) (m := m) (bs := p1)
      (hbs := hS.1.1) (hbs_bound := hS.2)
      (h_s_in := h_cov1) (h_x_in := h_cov2)
    · exact hS.1.2
  · have hX := props1.2.2.2.2 h1; have hW := props2.1 h2
    simp only [mem_targetsWin, mem_targetsW] at hW
    simp [h1, h2] at h_cov1 h_cov2
    rw [hX] at h_cov1
    apply disjoint_label_X_W (cp := cp) (m := m) (bw := p2)
      (hbw := hW.1.1) (hbw_pos := hW.2)
      (h_w_in := h_cov2) (h_x_in := h_cov1)
    · exact hW.1.2
  · have hX := props1.2.2.2.2 h1; have hN := props2.2.1 h2
    simp only [mem_targetsNin, mem_targetsN] at hN
    simp [h1, h2] at h_cov1 h_cov2
    rw [hX] at h_cov1
    apply disjoint_label_X_N (cp := cp) (m := m) (bn := p2)
      (hbn := hN.1.1) (hbn_pos := hN.2)
      (h_n_in := h_cov2) (h_x_in := h_cov1)
    · exact hN.1.2
  · have hX := props1.2.2.2.2 h1; have hE := props2.2.2.1 h2
    simp only [mem_targetsEin, mem_targetsE] at hE
    simp [h1, h2] at h_cov1 h_cov2
    rw [hX] at h_cov1
    apply disjoint_label_X_E (cp := cp) (m := m) (be := p2)
      (hbe := hE.1.1) (hbe_bound := hE.2)
      (h_x_in := h_cov1) (h_e_in := h_cov2)
    · exact hE.1.2
  · have hX := props1.2.2.2.2 h1; have hS := props2.2.2.2.1 h2
    simp only [mem_targetsSin, mem_targetsS] at hS
    simp [h1, h2] at h_cov1 h_cov2
    rw [hX] at h_cov1
    apply disjoint_label_X_S (cp := cp) (m := m) (bs := p2)
      (hbs := hS.1.1) (hbs_bound := hS.2)
      (h_s_in := h_cov2) (h_x_in := h_cov1)
    · exact hS.1.2
  · have hX1 := props1.2.2.2.2 h1; have hX2 := props2.2.2.2.2 h2
    have h_eq : l1 = l2 := by
      cases l1; cases l2
      simp only [Label.mk.injEq]
      dsimp at h1 h2 hX1 hX2
      constructor
      · rw [hX1, hX2]
      · rw [h1, h2]
    contradiction

lemma grid_size_ge_two_of_label {source : Point n} {lbl : LabelType}
    (ha_pos : 0 < c.a) (hb_pos : 0 < c.b)
    (hl : { source := source, type := lbl } ∈ c.validLabels cp) : 2 ≤ n := by
  simp only [validLabels, mem_union, mem_map, or_assoc] at hl
  rcases hl with h | h | h | h | h
  · simp at h; omega
  · simp at h; omega
  · simp at h; omega
  · simp at h; omega
  · have ha := c.a_ge_two ha_pos; have hb := c.b_ge_two hb_pos
    have h_card : c.u.card + c.v.card ≤ c.all_black.card := by
      rw [← card_union_of_disjoint c.h_disj]
      apply card_le_card
      apply union_subset c.hu_sub c.hv_sub
    rw [c.hu, c.hv, c.h_n] at h_card
    omega

lemma valid_label_pos_not_black (ha_pos : 0 < c.a) (hb_pos : 0 < c.b)
    (l : Label n) (hl : l ∈ c.validLabels cp) :
    (label_pos l).2 ∉ c.all_black := by
  have h_n_ge_2 := c.grid_size_ge_two_of_label cp ha_pos hb_pos hl
  intro h_pos_black
  rcases l with ⟨source, type⟩
  have h_n_ge_2 := c.grid_size_ge_two_of_label cp ha_pos hb_pos hl
  simp only [label_pos] at h_pos_black
  simp only [validLabels, mem_union, mem_map, or_assoc] at hl
  rcases hl with hW | hN | hE | hS | hX
  · rcases hW with ⟨p, hp, heq⟩
    simp at heq; obtain ⟨rfl, rfl⟩ := heq
    simp only [mem_targetsWin, mem_targetsW] at hp
    simp at h_pos_black
    have h_eq : p = (p.1, p.2 - 1) := by
       apply c.h_unique_x p hp.1.1 _ h_pos_black; simp
    replace h_eq := (Prod.ext_iff.mp h_eq).2
    apply (Fin.ext_iff).mp at h_eq
    have h_pos : 0 < p.2.val := hp.2
    have h_le : (1 : Fin n) ≤ p.2 := by
      simp [Fin.le_def]; rw [Nat.mod_eq_of_lt h_n_ge_2]
      exact Nat.succ_le_of_lt h_pos
    rw [Fin.sub_val_of_le h_le] at h_eq
    have : (1 : Fin n).val = 1 := by simp; rw [Nat.mod_eq_of_lt h_n_ge_2]
    omega
  · rcases hN with ⟨p, hp, heq⟩
    simp at heq; obtain ⟨rfl, rfl⟩ := heq
    simp only [mem_targetsNin, mem_targetsN] at hp
    simp at h_pos_black
    have h_eq : p = (p.1 - 1, p.2) := by
       apply c.h_unique_y p hp.1.1 _ h_pos_black; simp
    replace h_eq := (Prod.ext_iff.mp h_eq).1
    apply (Fin.ext_iff).mp at h_eq
    have h_pos : 0 < p.1.val := hp.2
    have h_le : (1 : Fin n) ≤ p.1 := by
      simp [Fin.le_def]; rw [Nat.mod_eq_of_lt h_n_ge_2]
      exact Nat.succ_le_of_lt h_pos
    rw [Fin.sub_val_of_le h_le] at h_eq
    have : (1 : Fin n).val = 1 := by simp; rw [Nat.mod_eq_of_lt h_n_ge_2]
    omega
  · rcases hE with ⟨p, hp, heq⟩
    simp at heq; obtain ⟨rfl, rfl⟩ := heq
    simp only [mem_targetsEin, mem_targetsE] at hp
    simp at h_pos_black
    have h_eq : p = (p.1, p.2 + 1) := by
       apply c.h_unique_x p hp.1.1 _ h_pos_black; simp
    replace h_eq := (Prod.ext_iff.mp h_eq).2
    apply (Fin.ext_iff).mp at h_eq
    have h_lt : p.2.val < n - 1 := hp.2
    rw [Fin.val_add] at h_eq
    simp at h_eq
    rw [Nat.mod_eq_of_lt (by omega)] at h_eq
    omega
  · rcases hS with ⟨p, hp, heq⟩
    simp at heq; obtain ⟨rfl, rfl⟩ := heq
    simp only [mem_targetsSin, mem_targetsS] at hp
    simp at h_pos_black
    have h_eq : p = (p.1 + 1, p.2) := by
       apply c.h_unique_y p hp.1.1 _ h_pos_black; simp
    replace h_eq := (Prod.ext_iff.mp h_eq).1
    apply (Fin.ext_iff).mp at h_eq
    have h_lt : p.1.val < n - 1 := hp.2
    rw [Fin.val_add] at h_eq
    simp at h_eq
    rw [Nat.mod_eq_of_lt (by omega)] at h_eq
    omega
  ·
    rcases hX with ⟨p, hp, heq⟩
    simp at heq; obtain ⟨rfl, rfl⟩ := heq
    simp at hp
    subst p
    simp at h_pos_black
    have h_not_black := c.wx_not_black cp
    contradiction

lemma card_validLabels_disjoint :
    (c.validLabels cp).card =
    (targetsWin c.u c.v c.all_black).card + (targetsNin c.u c.v c.all_black).card +
    (targetsEin c.u c.v c.all_black).card + (targetsSin c.u c.v c.all_black).card + 1 := by
  rw [validLabels]
  rw [card_union_of_disjoint]
  rw [card_union_of_disjoint]
  rw [card_union_of_disjoint]
  rw [card_union_of_disjoint]
  simp only [card_map, card_singleton]
  all_goals {
    try rw [disjoint_left]
    try intro x h1 h2
    try simp only [mem_union, mem_map, Function.Embedding.coeFn_mk] at h1 h2
    try {
      rcases x with ⟨src, type⟩
      try {
        simp at h2
        have h_black : c.wx cp ∈ c.all_black := by
             rcases h1 with ⟨_, h, _⟩ | ⟨_, h, _⟩ | ⟨_, h, _⟩ | ⟨_, h, _⟩
      }
      cases type <;> simp at h1 h2
    }
  }

theorem matilda_count_ge_label_count
  (ha_pos : 0 < c.a) (hb_pos : 0 < c.b)
  (matildas_partition : Finset (Matilda n c.all_black))
  (h_partition : ∀ p : Point n, p ∉ c.all_black → ∃! m ∈ matildas_partition, m.mem p) :
    (c.validLabels cp).card ≤ matildas_partition.card := by
  let f : { l // l ∈ c.validLabels cp } → { m // m ∈ matildas_partition } := fun ⟨l, hl⟩ =>
    have h_white : (label_pos l).2 ∉ c.all_black :=
      c.valid_label_pos_not_black cp ha_pos hb_pos l hl
    let m_obj := (h_partition (label_pos l).2 h_white).choose
    ⟨m_obj, (h_partition (label_pos l).2 h_white).choose_spec.1.1⟩

  have f_inj : Function.Injective f := by
    intro x1 x2 h_eq
    rcases x1 with ⟨l1, hl1⟩; rcases x2 with ⟨l2, hl2⟩
    simp only [f, Subtype.mk.injEq] at h_eq
    set M :=
      (h_partition (label_pos l1).2 (c.valid_label_pos_not_black cp ha_pos hb_pos l1 hl1)).choose
    have h_cov1 : c.covers M l1 :=
      (h_partition
       (label_pos l1).2 (c.valid_label_pos_not_black cp ha_pos hb_pos l1 hl1)).choose_spec.1.2
    have h_cov2 : c.covers M l2 := by
       rw [h_eq]
       exact (h_partition (label_pos l2).2
        (c.valid_label_pos_not_black cp ha_pos hb_pos l2 hl2)).choose_spec.1.2
    have h_at_most_one := c.matilda_covers_at_most_one cp M
    rw [card_le_one_iff] at h_at_most_one
    apply Subtype.ext
    apply h_at_most_one
    · simp; exact ⟨hl1, h_cov1⟩
    · simp; exact ⟨hl2, h_cov2⟩

  rw [← Fintype.card_coe (c.validLabels cp)]
  rw [← Fintype.card_coe matildas_partition]
  apply Fintype.card_le_of_injective f f_inj

theorem disjoint_case_final_bound
    (ha_pos : 0 < c.a) (hb_pos : 0 < c.b)
    (cp : c.CrossingPoints)
    (matildas_partition : Finset (Matilda n c.all_black))
    (h_partition : ∀ p : Point n, p ∉ c.all_black → ∃! m ∈ matildas_partition, m.mem p)
    (h_dilworth : n ≤ c.a * c.b) :
    n + (4 * n).sqrt - 3 ≤ matildas_partition.card := by
  have h_labels_ge : (c.validLabels cp).card ≥ n + c.a + c.b - 3 := by
    rw [c.card_validLabels_disjoint cp]
    apply c.labels_total_disjoint ha_pos hb_pos
  have h_matilda_ge : matildas_partition.card ≥ (c.validLabels cp).card :=
    c.matilda_count_ge_label_count cp ha_pos hb_pos matildas_partition h_partition
  have h_alg := am_gm_bound_nat c.a c.b n h_dilworth
  calc
    n + (4 * n).sqrt - 3
      ≤ n + (c.a + c.b) - 3     := Nat.sub_le_sub_right (Nat.add_le_add_left h_alg n) 3
    _ = n + c.a + c.b - 3       := by ring_nf
    _ ≤ (c.validLabels cp).card := h_labels_ge
    _ ≤ matildas_partition.card := h_matilda_ge

end DisjointSetup

section ErdosSzekeresBridge

variable {all_black : Finset (Point n)}
variable (h_card_n : all_black.card = n)
variable (h_unique_x : ∀ p ∈ all_black, ∀ q ∈ all_black, px p = px q → p = q)
variable (h_unique_y : ∀ p ∈ all_black, ∀ q ∈ all_black, py p = py q → p = q)

lemma exists_y_for_x [NeZero n] (h_card_n : all_black.card = n)
  (h_unique_x : ∀ p ∈ all_black, ∀ q ∈ all_black, px p = px q → p = q) (x : Fin n)
  : ∃ y, (x, y) ∈ all_black := by
  by_contra h_none
  push_neg at h_none
  let black_rows := all_black.image Prod.fst
  let other_rows := univ.erase x
  have h_subset : all_black.image Prod.fst ⊆ other_rows := by
    intro r hr
    rw [mem_image] at hr
    obtain ⟨p, hp, rfl⟩ := hr
    rw [mem_erase]
    constructor
    · by_contra h_eq
      have p_eq : p = (x, p.2) := by ext; rw [h_eq]; rfl
      rw [p_eq] at hp
      exact h_none p.2 hp
    · exact mem_univ p.1
  have h_inj_on : Set.InjOn Prod.fst (all_black : Set (Point n)) := by
    intros p hp q hq h_eq
    apply h_unique_x p hp q hq
    dsimp [px]; rw [h_eq]
  have h_card_le : all_black.card ≤ other_rows.card := calc
    all_black.card = black_rows.card := (card_image_of_injOn h_inj_on).symm
    _              ≤ other_rows.card := card_le_card h_subset
  rw [h_card_n] at h_card_le
  simp [other_rows , card_univ] at h_card_le
  have h_pos : 0 < n := NeZero.pos n
  omega

noncomputable def blackPerm [NeZero n] : Fin n → Fin n := fun x =>
  (exists_y_for_x h_card_n h_unique_x x).choose

lemma blackPerm_spec [NeZero n](x : Fin n) : (x, blackPerm h_card_n h_unique_x x) ∈ all_black :=
  (exists_y_for_x h_card_n h_unique_x x).choose_spec

lemma blackPerm_injective [NeZero n]
  (h_unique_y : ∀ p ∈ all_black, ∀ q ∈ all_black, py p = py q → p = q)
    : Function.Injective (blackPerm h_card_n h_unique_x) := by
  intros x1 x2 h_eq
  let p1 : Point n := (x1, blackPerm h_card_n h_unique_x x1)
  let p2 : Point n := (x2, blackPerm h_card_n h_unique_x x2)
  have m1 := blackPerm_spec h_card_n h_unique_x x1
  have m2 := blackPerm_spec h_card_n h_unique_x x2
  have hy : py p1 = py p2 := by simp [p1, p2, py]; rw [h_eq]
  have hp : p1 = p2 := h_unique_y p1 m1 p2 m2 hy
  injection hp

open Classical

def IsChain (s : Finset (Point n)) : Prop :=
  ∀ p ∈ s, ∀ q ∈ s, px p < px q → py p < py q
def IsAntiChain (s : Finset (Point n)) : Prop :=
  ∀ p ∈ s, ∀ q ∈ s, px p < px q → py q < py p

lemma exists_maximal_chain (s : Finset (Point n)) (h_s : s ⊆ all_black) (h_chain : IsChain s) :
    ∃ m, s ⊆ m ∧ m ⊆ all_black ∧ IsChain m ∧
    (∀ p, p ∉ m → p ∈ all_black → ¬IsChain (insert p m)) := by
  let all_chains := all_black.powerset.filter (fun t => s ⊆ t ∧ IsChain t)
  have h_nonempty : all_chains.Nonempty := by
    use s
    simp only [all_chains, mem_filter, mem_powerset]
    exact ⟨h_s, subset_refl _, h_chain⟩
  obtain ⟨m, hm_mem, hm_max⟩ := exists_mem_eq_sup all_chains h_nonempty card
  simp only [all_chains, mem_filter, mem_powerset] at hm_mem
  refine ⟨m, hm_mem.2.1, hm_mem.1, hm_mem.2.2, ?_⟩
  intros p hp_not_m hp_in_all h_chain_insert
  have h_in_chains : insert p m ∈ all_chains := by
    simp only [all_chains, mem_filter, mem_powerset]
    refine ⟨insert_subset hp_in_all hm_mem.1, ?_, h_chain_insert⟩
    trans m; exact hm_mem.2.1; exact subset_insert p m
  have h_card_gt : (insert p m).card > m.card := by simp [hp_not_m]
  have h_card_le : (insert p m).card ≤ m.card := by
    rw [← hm_max]; exact le_sup h_in_chains
  linarith

lemma exists_maximal_antichain (s : Finset (Point n))
  (h_s : s ⊆ all_black) (h_antichain : IsAntiChain s) :
    ∃ m, s ⊆ m ∧ m ⊆ all_black ∧ IsAntiChain m ∧
    (∀ p, p ∉ m → p ∈ all_black → ¬IsAntiChain (insert p m)) := by
  let all_antichains := all_black.powerset.filter (fun t => s ⊆ t ∧ IsAntiChain t)
  have h_nonempty : all_antichains.Nonempty := by
    use s
    simp only [all_antichains, mem_filter, mem_powerset]
    exact ⟨h_s, subset_refl _, h_antichain⟩
  obtain ⟨m, hm_mem, hm_max⟩ := exists_mem_eq_sup all_antichains h_nonempty card
  simp only [all_antichains, mem_filter, mem_powerset] at hm_mem
  refine ⟨m, hm_mem.2.1, hm_mem.1, hm_mem.2.2, ?_⟩
  intros p hp_not_m hp_in_all h_antichain_insert
  have h_in_chains : insert p m ∈ all_antichains := by
    simp only [all_antichains, mem_filter, mem_powerset]
    refine ⟨insert_subset hp_in_all hm_mem.1, ?_, h_antichain_insert⟩
    trans m; exact hm_mem.2.1; exact subset_insert p m
  have h_card_gt : (insert p m).card > m.card := by simp [hp_not_m]
  have h_card_le : (insert p m).card ≤ m.card := by
    rw[← hm_max]; exact le_sup h_in_chains
  linarith

def incSubsets (f : Fin n → Fin n) : Finset (Finset (Fin n)) :=
  univ.powerset.filter (fun t => StrictMonoOn f (t : Set (Fin n)))
def decSubsets (f : Fin n → Fin n) : Finset (Finset (Fin n)) :=
  univ.powerset.filter (fun t => StrictAntiOn f (t : Set (Fin n)))

@[simp]
lemma mem_incSubsets {f : Fin n → Fin n} {t : Finset (Fin n)} :
    t ∈ incSubsets f ↔ StrictMonoOn f (t : Set (Fin n)) := by
  simp [incSubsets]
@[simp]
lemma mem_decSubsets {f : Fin n → Fin n} {t : Finset (Fin n)} :
    t ∈ decSubsets f ↔ StrictAntiOn f (t : Set (Fin n)) := by
  simp [decSubsets]

lemma incSubsets_nonempty (f : Fin n → Fin n) : (incSubsets f).Nonempty := by
  use ∅; simp [incSubsets, StrictMonoOn]
lemma decSubsets_nonempty (f : Fin n → Fin n) : (decSubsets f).Nonempty := by
  use ∅; simp [decSubsets, StrictAntiOn]

noncomputable def lisLength (f : Fin n → Fin n) : ℕ :=
  (incSubsets f).sup card
noncomputable def ldsLength (f : Fin n → Fin n) : ℕ :=
  (decSubsets f).sup card

theorem erdos_szekeres_direct (n : ℕ) (f : Fin n → Fin n) (hf : Function.Injective f) :
    n ≤ (lisLength f) * (ldsLength f) := by
  let a := lisLength f
  let b := ldsLength f
  by_contra h_contra
  rw [not_le] at h_contra
  have h_card_lt : a * b < Fintype.card (Fin n) := by
    rw [Fintype.card_fin]
    exact h_contra
  have h_thm := Theorems100.erdos_szekeres h_card_lt hf

  rcases h_thm with ⟨t_inc, _, h_mono_inc⟩ | ⟨t_dec, _, h_mono_dec⟩
  · have h_mem : t_inc ∈ incSubsets f := by
      simp [incSubsets]; exact h_mono_inc
    have h_le : t_inc.card ≤ a := le_sup h_mem
    linarith
  · have h_mem : t_dec ∈ decSubsets f := by
      simp [decSubsets]; exact h_mono_dec
    have h_le : t_dec.card ≤ b := le_sup h_mem
    linarith

def toGridSubset (f : Fin n → Fin n) (t : Finset (Fin n)) : Finset (Point n) :=
  t.image (fun r => (r, f r))

@[simp]
lemma card_toGridSubset (f : Fin n → Fin n) (t : Finset (Fin n)) :
    (toGridSubset f t).card = t.card :=
  card_image_of_injective t (fun _ _ h => by injection h)

lemma is_chain_of_strict_mono {f : Fin n → Fin n} {t : Finset (Fin n)}
    (h : StrictMonoOn f t) : IsChain (toGridSubset f t) := by
  intros p hp q hq hx
  simp [toGridSubset] at hp hq
  rcases hp with ⟨r1, hr1, rfl⟩
  rcases hq with ⟨r2, hr2, rfl⟩
  simp only [px_mk_val] at hx
  have h_val_lt : r1.val < r2.val := hx
  have h_r_lt : r1 < r2 := Fin.lt_def.mpr h_val_lt
  have h_f_lt : f r1 < f r2 := h hr1 hr2 h_r_lt
  simp only [py_mk_val]; exact h_f_lt

lemma is_antichain_of_strict_anti {f : Fin n → Fin n} {t : Finset (Fin n)}
    (h : StrictAntiOn f t) : IsAntiChain (toGridSubset f t) := by
  intros p hp q hq hx
  simp [toGridSubset] at hp hq
  rcases hp with ⟨r1, hr1, rfl⟩
  rcases hq with ⟨r2, hr2, rfl⟩
  simp only [px_mk_val] at hx
  have h_r_lt : r1 < r2 := Fin.lt_def.mpr hx
  have h_f_lt : f r2 < f r1 := h hr1 hr2 h_r_lt
  simp only [py_mk_val]; exact h_f_lt

theorem exists_optimal_u_v [NeZero n] (h_card_n : all_black.card = n)
   (h_unique_x : ∀ p ∈ all_black, ∀ q ∈ all_black, px p = px q → p = q)
   (h_unique_y : ∀ p ∈ all_black, ∀ q ∈ all_black, py p = py q → p = q) :

    ∃ (u v : Finset (Point n)),
      u ⊆ all_black ∧ v ⊆ all_black ∧
      n ≤ u.card * v.card ∧
      (∀ p ∈ u, ∀ q ∈ u, px p < px q → py p < py q) ∧
      (∀ p ∈ u, ∀ q ∈ u, px p = px q → p = q) ∧
      (∀ p ∈ all_black, p ∉ u →
        (∀ q ∈ u, px q < px p → py q < py p) →
        (∀ q ∈ u, px p < px q → py p < py q) → False) ∧
      (∀ p ∈ v, ∀ q ∈ v, px p < px q → py q < py p) ∧
      (∀ p ∈ v, ∀ q ∈ v, px p = px q → p = q) ∧
      (∀ p ∈ all_black, p ∉ v →
        (∀ q ∈ v, px q < px p → py p < py q) →
        (∀ q ∈ v, px p < px q → py q < py p) → False) := by
  let f := blackPerm h_card_n h_unique_x
  have hf_inj := blackPerm_injective h_card_n h_unique_x h_unique_y
  have h_es := erdos_szekeres_direct n f hf_inj
  obtain ⟨t_inc, ht_inc, ha_eq⟩ :=
  exists_mem_eq_sup (incSubsets f) (incSubsets_nonempty f) card
  obtain ⟨t_dec, ht_dec, hb_eq⟩ :=
    exists_mem_eq_sup (decSubsets f) (decSubsets_nonempty f) card
  let u0 := toGridSubset f t_inc
  let v0 := toGridSubset f t_dec
  have h_u0_sub : u0 ⊆ all_black := by
    intros p hp; simp [u0, toGridSubset] at hp
    rcases hp with ⟨r, _, rfl⟩; exact blackPerm_spec h_card_n h_unique_x r
  have h_v0_sub : v0 ⊆ all_black := by
    intros p hp; simp [v0, toGridSubset] at hp
    rcases hp with ⟨r, _, rfl⟩; exact blackPerm_spec h_card_n h_unique_x r

  have h_u0_chain : IsChain u0 := by
    rw [mem_incSubsets] at ht_inc; apply is_chain_of_strict_mono ht_inc
  have h_v0_antichain : IsAntiChain v0 := by
    rw [mem_decSubsets] at ht_dec; apply is_antichain_of_strict_anti ht_dec
  obtain ⟨u, hu_sub, hu_all, hu_chain, hu_max⟩ :=
    exists_maximal_chain u0 h_u0_sub h_u0_chain
  obtain ⟨v, hv_sub, hv_all, hv_chain, hv_max⟩ :=
    exists_maximal_antichain v0 h_v0_sub h_v0_antichain
  use u, v
  have h_dilworth : n ≤ u.card * v.card := by
    have h_a : lisLength f ≤ u.card := by
      simp only [lisLength]; rw [ha_eq, ← card_toGridSubset f t_inc]
      exact card_le_card hu_sub
    have h_b : ldsLength f ≤ v.card := by
      simp only [ldsLength]; rw [hb_eq, ← card_toGridSubset f t_dec]
      exact card_le_card hv_sub
    calc n ≤ lisLength f * ldsLength f := h_es
         _ ≤ u.card * v.card := Nat.mul_le_mul h_a h_b

  refine ⟨hu_all, hv_all, h_dilworth, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hu_chain
  · intros p _ q _ hx
    exact h_unique_x p (hu_all ‹_›) q (hu_all ‹_›) hx
  · intros p hp_blk hp_not_u h_left h_right
    apply hu_max p hp_not_u hp_blk
    intros a ha b hb hx
    simp at ha hb
    rcases ha with rfl | ha_u; rcases hb with rfl | hb_u
    · linarith
    · apply h_right b hb_u hx
    · rcases hb with rfl | hb_u
      · exact h_left a ha_u hx
      · exact hu_chain a ha_u b hb_u hx
  · exact hv_chain
  · intros p _ q _ hx
    exact h_unique_x p (hv_all ‹_›) q (hv_all ‹_›) hx
  · intros p hp_blk hp_not_v h_left h_right
    apply hv_max p hp_not_v hp_blk
    intros a ha b hb hx
    simp at ha hb
    rcases ha with rfl | ha_v; rcases hb with rfl | hb_v
    · linarith
    · apply h_right b hb_v hx
    · rcases hb with rfl | hb_v
      · exact h_left a ha_v hx
      · exact hv_chain a ha_v b hb_v hx

end ErdosSzekeresBridge

section LowerBound

theorem matilda_lower_bound [NeZero n]
    (h_card_n : all_black.card = n)
    (h_unique_x : ∀ p ∈ all_black, ∀ q ∈ all_black, px p = px q → p = q)
    (h_unique_y : ∀ p ∈ all_black, ∀ q ∈ all_black, py p = py q → p = q)
    (matildas_partition : Finset (Matilda n all_black))
    (h_partition : ∀ p : Point n, p ∉ all_black → ∃! m ∈ matildas_partition, m.mem p) :
    n + (4 * n).sqrt - 3 ≤ matildas_partition.card := by
  obtain ⟨u, v, hu_sub, hv_sub, h_dilworth,
          h_u_mono, h_u_inj, h_u_max,
          h_v_mono, h_v_inj, h_v_max⟩ :=
    exists_optimal_u_v h_card_n h_unique_x h_unique_y
  have ha_pos : 0 < u.card := by
    have : 1 ≤ n := NeZero.one_le
    have h_mul : 1 ≤ u.card * v.card := le_trans this h_dilworth
    rw [Nat.one_le_iff_ne_zero] at h_mul
    exact Nat.pos_of_ne_zero (left_ne_zero_of_mul h_mul)

  have hb_pos : 0 < v.card := by
    have : 1 ≤ n := NeZero.one_le
    have h_mul: 1 ≤ u.card * v.card := le_trans this h_dilworth
    rw [Nat.one_le_iff_ne_zero] at h_mul
    exact Nat.pos_of_ne_zero (right_ne_zero_of_mul h_mul)
  by_cases h_inter : (u ∩ v).Nonempty
  · let pivot := h_inter.choose
    have h_pivot_mem : pivot ∈ u ∩ v := h_inter.choose_spec
    have h_inter_eq : u ∩ v = {pivot} := by
      have h_le_one := inter_card_le_one h_u_mono h_v_mono h_u_inj
      apply eq_singleton_iff_unique_mem.mpr
      constructor
      · exact h_pivot_mem
      · intros x hx
        rw [card_le_one_iff] at h_le_one
        exact h_le_one hx h_pivot_mem
    let c : IntersectionSetup n := {
      all_black := all_black
      u := u
      v := v
      pivot := pivot
      a := u.card
      b := v.card
      hu := rfl
      hv := rfl
      h_n := h_card_n
      hu_sub := hu_sub
      hv_sub := hv_sub
      h_inter := h_inter_eq
      h_u_mono := h_u_mono
      h_v_mono := h_v_mono
      h_u_inj := h_u_inj
      h_v_inj := h_v_inj
      h_u_max := h_u_max
      h_v_max := h_v_max
      h_unique_x := h_unique_x
      h_unique_y := h_unique_y
    }

    apply c.intersection_case_final_bound  matildas_partition h_partition h_dilworth

  · rw [not_nonempty_iff_eq_empty] at h_inter
    have h_disjoint : Disjoint u v := disjoint_iff_inter_eq_empty.mpr h_inter
    let c : DisjointSetup n := {
      all_black := all_black
      u := u
      v := v
      a := u.card
      b := v.card
      hu := rfl
      hv := rfl
      hu_sub := hu_sub
      hv_sub := hv_sub
      h_n := h_card_n
      h_disj := h_disjoint
      h_u_mono := h_u_mono
      h_v_mono := h_v_mono
      h_u_inj := h_u_inj
      h_v_inj := h_v_inj
      h_u_max := h_u_max
      h_v_max := h_v_max
      h_unique_x := h_unique_x
      h_unique_y := h_unique_y
    }

    let cp := c.getCrossingPoints ha_pos hb_pos
    apply c.disjoint_case_final_bound ha_pos hb_pos cp matildas_partition h_partition h_dilworth

end LowerBound

section Construction

variable (k : ℕ)
local notation "n" => k * k
abbrev mod_base : ℤ := (k : ℤ)^2 + 1
abbrev val_s (p : Point n) : ℤ := (p.1 : ℤ) + k * p.2 + k + 1
abbrev val_t (p : Point n) : ℤ := (k : ℤ) * p.1 - p.2 + k^2 + k

def calc_s (p : Point n) : Int := (val_s k p) / (mod_base k)
def calc_t (p : Point n) : Int := (val_t k p) / (mod_base k)
def all_black_k : Finset (Point n) :=
  univ.filter fun p =>
    ((val_s k p) % (mod_base k) == 0) ∧ ((val_t k p) % (mod_base k) == 0)

@[simp]
def b_st_coords (s t : Int) : Int × Int := ((s - 1) + (t - 1) * k, s * k - t)
def make_b_point (s t : Int)
    (h_bounds : let b := b_st_coords k s t
                0 ≤ b.1 ∧ b.1 < n ∧ 0 ≤ b.2 ∧ b.2 < n) : Point n :=
  let b := b_st_coords k s t
  ⟨⟨b.1.toNat,
    by zify [h_bounds.1]; rw [Int.toNat_of_nonneg h_bounds.1]; exact h_bounds.2.1⟩,
   ⟨b.2.toNat,
    by zify [h_bounds.2.2.1]; rw [Int.toNat_of_nonneg h_bounds.2.2.1]; exact h_bounds.2.2.2⟩⟩
def M_st (s t : Int) : Finset (Point n) :=
  univ.filter fun p => p ∉ all_black_k k ∧ calc_s k p = s ∧ calc_t k p = t
def in_white_rect (s t : Int) (p : Point n) : Prop :=
  ((s - 1) + (t - 1) * k + 1 ≤ (p.1 : ℤ) ∧ (p.1 : ℤ) ≤ (s - 1) + t * k) ∧
  (s * k - t ≤ (p.2 : ℤ) ∧ (p.2 : ℤ) ≤ (s + 1) * k - t - 1)

structure BlackPointProps (s t : Int) (p : Point n) : Prop where
  is_s : calc_s k p = s
  is_t : calc_t k p = t
  is_black : p ∈ all_black_k k

lemma b_st_props (s t : Int)
    (h_bounds : let b := b_st_coords k s t
                0 ≤ b.1 ∧ b.1 < n ∧ 0 ≤ b.2 ∧ b.2 < n) :
    BlackPointProps k s t (make_b_point k s t h_bounds) := by
  let p := make_b_point k s t h_bounds
  have h_pos : 0 < mod_base k := by exact Int.add_pos_of_nonneg_of_pos (sq_nonneg _) (by decide)
  have h_coords : (p.1 : ℤ) = (b_st_coords k s t).1 ∧ (p.2 : ℤ) = (b_st_coords k s t).2 := by
    dsimp [p, make_b_point]
    exact ⟨Int.toNat_of_nonneg h_bounds.1, Int.toNat_of_nonneg h_bounds.2.2.1⟩
  have h_vals : val_s k p = s * mod_base k ∧ val_t k p = t * mod_base k := by
    constructor <;> {
      dsimp [val_s, val_t]; rw [h_coords.1, h_coords.2]; dsimp; ring
    }
  constructor
  · rw [calc_s, h_vals.1]; exact Int.mul_ediv_cancel _ (ne_of_gt h_pos)
  · rw [calc_t, h_vals.2]; exact Int.mul_ediv_cancel _ (ne_of_gt h_pos)
  · simp only [all_black_k, mem_filter, mem_univ, true_and]
    rw [beq_iff_eq, beq_iff_eq]; rw [h_vals.1, h_vals.2];
    exact ⟨Int.mul_emod_left _ _, Int.mul_emod_left _ _⟩

lemma M_subset_rect (s t : Int) (p : Point n) (hk : 2 ≤ k) :
    p ∈ M_st k s t → in_white_rect k s t p := by
  intro h_mem
  rw [M_st, mem_filter] at h_mem
  obtain ⟨_, hp_white, hs_eq, ht_eq⟩ := h_mem
  let M := mod_base k
  have h_pos : 0 < M := by nlinarith
  have hk_pos : 0 < (k:ℤ) := by omega
  let xb := (s - 1) + (t - 1) * k
  let yb := s * k - t
  have h_s := hs_eq
  unfold calc_s at h_s
  rw [Int.ediv_eq_iff_of_pos (by dsimp [M, mod_base]; nlinarith)] at h_s
  have h_t := ht_eq
  rw [calc_t, Int.ediv_eq_iff_of_pos (by dsimp [M, mod_base]; nlinarith)] at h_t
  have h_diff_x : M * (p.1 - xb) = (val_s k p - s * M) + k * (val_t k p - t * M) := by
    dsimp [val_s, val_t, M, xb]; ring
  have h_diff_y : M * (p.2 - yb) = (k : ℤ) * (val_s k p - s * M) - (val_t k p - t * M) := by
    dsimp [val_s, val_t, M, yb]; ring
  constructor
  · constructor
    · have h_ge_0 : 0 ≤ (p.1 : ℤ) - xb := by
        apply Int.nonneg_of_mul_nonneg_left _ h_pos
        rw [mul_comm]; rw [h_diff_x]; nlinarith [h_s.1, h_t.1]
      have h_ne_0 : (p.1 : ℤ) - xb ≠ 0 := by
        intro h_zero
        have h_sum_zero : (val_s k p - s * M) + k * (val_t k p - t * M) = 0 := by
          rw [← h_diff_x, h_zero, mul_zero]
        have h_vs : val_s k p = s * M := by
          have : 0 ≤ val_t k p - t * M := by linarith [h_t.1]
          nlinarith [h_s.1, h_sum_zero, (by omega : 0 < (k:ℤ))]
        have h_vt : val_t k p = t * M := by
          rw [h_vs] at h_sum_zero
          simp only [sub_self, zero_add] at h_sum_zero
          replace h_sum_zero := Int.mul_eq_zero.mp h_sum_zero |>.resolve_left hk_pos.ne'
          linarith
        have h_is_black : p ∈ all_black_k k := by
          simp [all_black_k]
          rw [h_vs, h_vt]
          dsimp [M]; simp
        contradiction
      omega
    · have : M * (p.1 - xb) < M * (k + 1) := by
        rw [h_diff_x]
        calc (val_s k p - s * M) + k * (val_t k p - t * M)
          _ < M + k * M := by gcongr; linarith; linarith
          _ = M * (k + 1) := by ring
      rw [Int.mul_lt_mul_left (by dsimp [M, mod_base]; nlinarith)] at this
      linarith
  · constructor
    · have h_yb_le : yb ≤ (p.2 : ℤ) := by
        have h_scaled : M * (yb - 1) < M * p.2 := by
          dsimp [yb]
          calc M * (s * k - t - 1)
            _ = (k : ℤ) * (s * M) - (t + 1) * M := by dsimp [M]; ring
            _ ≤ (k : ℤ) * val_s k p - (t + 1) * M := by gcongr; exact h_s.1
            _ < (k : ℤ) * val_s k p - val_t k p := by linarith [h_t.2]
            _ = M * p.2 := by
              linarith [h_diff_y]
        have h_lt : yb - 1 < (p.2 : ℤ) := by
          rwa [mul_lt_mul_iff_right₀ h_pos] at h_scaled
        linarith
      exact h_yb_le
    · have : M * p.2 < M * ((s + 1) * k - t) := by
        have h_linear_y_orig : (k : ℤ) * val_s k p - val_t k p = M * p.2 := by
            dsimp [val_s, val_t, M]; ring
        rw [← h_linear_y_orig]
        calc (k : ℤ) * val_s k p - val_t k p
          _ ≤ (k : ℤ) * val_s k p - t * M := by gcongr; exact h_t.1
          _ < (k : ℤ) * ((s + 1) * M) - t * M := by gcongr; linarith [h_s.2]
          _ = M * ((s + 1) * k - t) := by dsimp [M]; ring
      rw [mul_lt_mul_iff_right₀ (by dsimp [M, mod_base]; nlinarith)] at this
      exact Int.le_sub_one_of_lt this

lemma rect_subset_M (s t : Int) (p : Point n)
    (hk : 2 ≤ k) :
    in_white_rect k s t p → p ∈ M_st k s t := by
  intro h_rect
  let M := mod_base k
  have h_pos : 0 < M := by apply Int.add_pos_of_nonneg_of_pos (sq_nonneg _) (by decide)
  rcases h_rect with ⟨⟨hx_ge, hx_le⟩, ⟨hy_ge, hy_le⟩⟩
  have h_val_s_strict : s * M < val_s k p ∧ val_s k p < (s + 1) * M := by
    constructor
    · calc s * M
        _ = ((s - 1) + (t - 1) * k + 1) + k * (s * k - t) + k + 1 - val_s k p + val_s k p -1 := by
            dsimp [val_s, M]; ring
        _ ≤ p.1 + k * p.2 + k := by
            dsimp [val_s]; simp; gcongr
        _ = val_s k p - 1 := by ring
        _ < val_s k p := by linarith
    · calc val_s k p
        _ = p.1 + k * p.2 + k + 1 := rfl
        _ ≤ ((s - 1) + t * k) + k * ((s + 1) * k - t - 1) + k + 1 := by gcongr
        _ = s * M + k^2 := by dsimp [M]; ring
        _ < s * M + (k^2 + 1) := by linarith
        _ = (s + 1) * M := by dsimp [M]; ring
  have h_val_t_strict : t * M < val_t k p ∧ val_t k p < (t + 1) * M := by
    constructor
    · calc t * M
        _ = k * ((s - 1) + (t - 1) * k + 1) - ((s + 1) * k - t - 1) + k^2 + k - 1 := by
             dsimp [val_t, M]; ring
        _ ≤ k * p.1 - p.2 + k^2 + k - 1 := by gcongr
        _ = val_t k p - 1 := by ring
        _ < val_t k p := by linarith
    · calc val_t k p
        _ = k * p.1 - p.2 + k^2 + k := rfl
        _ ≤ k * ((s - 1) + t * k) - (s * k - t) + k^2 + k := by gcongr
        _ = t * M + k^2 := by dsimp [M]; ring
        _ < t * M + (k^2 + 1) := by linarith
        _ = (t + 1) * M := by dsimp [M]; ring
  simp only  [M_st, mem_filter, mem_univ, true_and]
  constructor
  · simp only [all_black_k, mem_filter]
    rw [not_and_or]
    right
    rw [beq_iff_eq]
    have h_val_s_mod_ne_zero: val_s k p % M ≠ 0 := by
      rw [← Int.sub_mul_emod_self_right (val_s k p) s M]
      have h_diff_pos : 0 < val_s k p - s * M := by linarith [h_val_s_strict.1]
      have h_diff_lt  : val_s k p - s * M < M := by linarith [h_val_s_strict.2]
      rw [Int.emod_eq_of_lt (le_of_lt h_diff_pos) h_diff_lt]
      exact ne_of_gt h_diff_pos
    change ¬(val_s k p % M = 0 ∧ _)
    simp [h_val_s_mod_ne_zero]
  · constructor
    · rw [calc_s]
      rw [Int.ediv_eq_iff_of_pos h_pos]
      constructor
      · exact le_of_lt h_val_s_strict.1
      · linarith [h_val_s_strict.2]
    · rw [calc_t]
      rw [Int.ediv_eq_iff_of_pos h_pos]
      constructor
      · exact le_of_lt h_val_t_strict.1
      · linarith [h_val_t_strict.2]

instance (k : ℕ) (s t : Int) : DecidablePred (in_white_rect k s t) := by
  intro p; unfold in_white_rect; infer_instance

def rect_finset (s t : Int) : Finset (Point n) :=
  univ.filter (in_white_rect k s t)

lemma M_st_eq_rect (s t : Int) (hk : 2 ≤ k) :
    M_st k s t = rect_finset k s t := by
  ext p
  simp only [rect_finset, mem_filter, mem_univ, true_and]
  constructor
  · exact M_subset_rect k s t p hk
  · exact rect_subset_M k s t p hk

lemma mem_rect_iff_idx_eq (p : Point (k * k)) (s t : ℤ) (hk : 2 ≤ k) :
    p ∈ rect_finset k s t ↔ (p ∉ all_black_k k ∧ calc_s k p = s ∧ calc_t k p = t) := by
  rw [← M_st_eq_rect k s t hk]
  simp [M_st]

lemma s_t_range (hk : 2 ≤ k) (p : Point n) :
    0 ≤ calc_s k p ∧ calc_s k p ≤ k ∧
    0 ≤ calc_t k p ∧ calc_t k p ≤ k := by
  let M := mod_base k
  have h_pos : 0 < M := by apply Int.add_pos_of_nonneg_of_pos (sq_nonneg _) (by decide)
  have h_pos' : 0 < mod_base k := by dsimp [M] at h_pos; exact h_pos
  have hk_pos : 0 < (k : ℤ) := by omega
  have hx : 0 ≤ (p.1 : ℤ) ∧ (p.1 : ℤ) ≤ k^2 - 1 := by
    constructor
    · exact Int.natCast_nonneg _
    · have h := p.1.isLt
      zify at h; linarith
  have hy : 0 ≤ (p.2 : ℤ) ∧ (p.2 : ℤ) ≤ k^2 - 1 := by
    constructor
    · exact Int.natCast_nonneg _
    · have h := p.2.isLt
      zify at h; linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [calc_s]
    apply Int.ediv_nonneg
    · dsimp [val_s]; nlinarith
    · exact le_of_lt h_pos
  · dsimp [calc_s]
    rw [Int.le_iff_lt_add_one]
    rw [Int.ediv_lt_iff_lt_mul h_pos]
    dsimp [val_s, M, mod_base]
    calc (p.1 : ℤ) + k * p.2 + k + 1
      _ ≤ (k^2 - 1) + k * (k^2 - 1) + k + 1 := by gcongr; exact hx.2; exact hy.2
      _ = k^3 + k^2 := by ring
      _ < k^3 + k^2 + k + 1 := by linarith
      _ = (k+1) * (k^2 + 1) := by ring
  · rw [calc_t]
    apply Int.ediv_nonneg
    · dsimp [val_t]; nlinarith
    · exact le_of_lt h_pos
  · dsimp [calc_t]
    rw [Int.le_iff_lt_add_one]
    rw [Int.ediv_lt_iff_lt_mul h_pos]
    dsimp [val_t, M, mod_base]
    calc (k:ℤ) * p.1 - p.2 + k^2 + k
      _ ≤ k * (k^2 - 1) - 0 + k^2 + k := by gcongr; exact hx.2; exact hy.1
      _ = (k + 1) * k^2 := by ring
      _ < k^3 + k^2 + k + 1 := by linarith
      _ = (k+1) * (k^2 + 1) := by ring

lemma M_00_empty (hk : 2 ≤ k) : M_st k 0 0 = ∅ := by
  rw [eq_empty_iff_forall_notMem]
  intro p hp
  rw [M_st, mem_filter] at hp
  obtain ⟨_, _, hs, ht⟩ := hp
  let M := mod_base k
  have h_pos : 0 < M := by apply Int.add_pos_of_nonneg_of_pos (sq_nonneg _) (by decide)
  have hk_pos : 0 < (k : ℤ) := by omega
  rw [calc_s, Int.ediv_eq_iff_of_pos h_pos] at hs
  rw [calc_t, Int.ediv_eq_iff_of_pos h_pos] at ht
  simp only [Int.zero_mul, Int.zero_add] at hs ht
  have h_y_lower : (k : ℤ) * p.1 + k ≤ p.2 := by
    dsimp [val_t, M] at ht
    linarith [ht.2]
  have h_contra : val_s k p > (k : ℤ)^2 + k := by
    calc val_s k p
      _ = p.1 + k * p.2 + k + 1 := rfl
      _ ≥ p.1 + k * (k * p.1 + k) + k + 1 := by gcongr
      _ = p.1 * (1 + k^2) + k^2 + k + 1 := by ring
      _ ≥ 0 * (1 + k^2) + k^2 + k + 1 := by gcongr; exact Int.natCast_nonneg p.1
      _ = k^2 + k + 1 := by ring
      _ > k^2 + k := by linarith
  dsimp [M] at hs
  linarith [hs.2, h_contra, (by omega : 0 < (k : ℤ))]

lemma M_k0_empty : M_st k k 0 = ∅ := by
  rw [eq_empty_iff_forall_notMem]
  intro p hp
  simp only [M_st, mem_filter, mem_univ, true_and] at hp
  obtain ⟨_, hs, ht⟩ := hp
  let M := mod_base k
  have h_pos : 0 < M := by apply Int.add_pos_of_nonneg_of_pos (sq_nonneg _) (by decide)
  rw [calc_s, Int.ediv_eq_iff_of_pos h_pos] at hs
  rw [calc_t, Int.ediv_eq_iff_of_pos h_pos] at ht
  simp only [Int.zero_mul, Int.zero_add] at hs ht
  have h_y_upper : (p.2 : ℤ) < k^2 := by
    let hp_lt := p.2.isLt
    zify at hp_lt; rw [pow_two]; exact hp_lt
  have h_y_ge : (p.2 : ℤ) ≥ k * p.1 + k := by
    dsimp [val_t, M] at ht
    linarith [ht.2]
  have h_s_bound : (p.1 : ℤ) + k * p.2 ≥ k^3 - 1 := by
    dsimp [val_s, M] at hs
    linarith [hs.1]
  nlinarith [h_y_ge, h_s_bound, h_y_upper]

lemma M_0k_empty (hk : 2 ≤ k) : M_st k 0 k = ∅ := by
  rw [eq_empty_iff_forall_notMem]
  intro p hp
  simp only [M_st, mem_filter, mem_univ, true_and] at hp
  obtain ⟨_, hs, ht⟩ := hp
  let M := mod_base k
  have h_pos : 0 < M := by apply Int.add_pos_of_nonneg_of_pos (sq_nonneg _) (by decide)
  rw [calc_s, Int.ediv_eq_iff_of_pos h_pos] at hs
  rw [calc_t, Int.ediv_eq_iff_of_pos h_pos] at ht
  simp only [Int.zero_mul, Int.zero_add] at hs
  have h_s_upper : (p.1 : ℤ) + k * p.2 < k^2 - k := by
    dsimp [val_s, M] at hs
    linarith [hs.2]
  have h_t_lower : (k : ℤ) * p.1 - p.2 ≥ k^3 - k^2 := by
    dsimp [val_t, M] at ht
    linarith [ht.1]
  have hp_y_nonneg : 0 ≤ (p.2 : ℤ) := Int.natCast_nonneg p.2
  nlinarith [h_s_upper, h_t_lower, hp_y_nonneg]

lemma M_kk_empty (_ : 2 ≤ k) : M_st k k k = ∅ := by
  rw [eq_empty_iff_forall_notMem]
  intro p hp
  simp only [M_st, mem_filter, mem_univ, true_and] at hp
  obtain ⟨_, hs, ht⟩ := hp
  let M := mod_base k
  have h_pos : 0 < M := by apply Int.add_pos_of_nonneg_of_pos (sq_nonneg _) (by decide)
  rw [calc_s, Int.ediv_eq_iff_of_pos h_pos] at hs
  rw [calc_t, Int.ediv_eq_iff_of_pos h_pos] at ht
  have h_x_bound : (p.1 : ℤ) ≤  k^2 - 1 := by
    let hp_lt := p.1.isLt
    zify at hp_lt; rw [pow_two]; exact Int.le_sub_one_of_lt hp_lt
  have h_y_bound : (p.2 : ℤ) ≤  k^2 - 1  := by
    let hp_lt := p.2.isLt
    zify at hp_lt; rw [pow_two]; exact Int.le_sub_one_of_lt hp_lt
  have h_t_ge : (k : ℤ) * p.1 - p.2 + k^2 + k ≥ k * M := ht.1
  have h_s_ge : (p.1 : ℤ) + k * p.2 + k + 1 ≥ k * M := hs.1
  dsimp [val_s, val_t, M] at h_t_ge h_s_ge
  have h_combine : (k : ℤ) * (k * p.1 - p.2 + k^2 + k) + (p.1 + k * p.2 + k + 1)
    ≥ (k : ℤ) * (k * M) + k * M := by nlinarith [h_t_ge, h_s_ge]
  have h_x_eq : (p.1 : ℤ) = k^2 - 1 := by
    dsimp [M, mod_base] at h_combine
    have h_lhs: (k : ℤ) * (k * p.1 - p.2 + k^2 + k) + (p.1 + k * p.2 + k + 1)
         = (k^2 + 1) * p.1 + (k^3 + k^2 + k + 1) := by ring
    rw [h_lhs] at h_combine
    have h_rhs: (k : ℤ) * (k * (k^2 + 1)) + k * (k^2 + 1)
         = (k^2 + 1) * (k^2 + k) := by ring
    rw [h_rhs] at h_combine
    nlinarith [h_x_bound, h_combine, (by omega : 0 < (k : ℤ))]
  have h_y_eq : (p.2 : ℤ) = k^2 - k := by
    rw [h_x_eq] at h_s_ge h_t_ge
    dsimp [M, mod_base] at h_s_ge h_t_ge
    apply le_antisymm
    · linarith [h_t_ge, h_s_ge]
    · nlinarith [h_t_ge, h_s_ge]
  have h_black : p ∈ all_black_k k := by
    simp only [all_black_k, mem_filter, mem_univ, true_and]
    rw [beq_iff_eq, beq_iff_eq]
    constructor
    · dsimp [val_s, M, mod_base]
      rw [h_x_eq, h_y_eq]
      have h_eq: (k^2 - 1 : ℤ) + k * (k^2 - k) + k + 1 = k * (k^2 + 1) := by ring
      rw [h_eq]
      exact Int.mul_emod_left _ _
    · dsimp [val_t, M, mod_base]
      rw [h_x_eq, h_y_eq]
      have h_eq: (k : ℤ) * (k^2 - 1) - (k^2 - k) + k^2 + k = k * (k^2 + 1) := by ring
      rw [h_eq]
      exact Int.mul_emod_left _ _
  contradiction

def clipped_rect [NeZero k] (hk : 2 ≤ k) (s t : Int) : Option (Matilda (k * k) (all_black_k k)) :=
  let r_xmin := (s - 1) + (t - 1) * k + 1
  let r_xmax := (s - 1) + t * k
  let r_ymin := s * k - t
  let r_ymax := (s + 1) * k - t - 1
  let new_xmin := max 0 r_xmin
  let new_xmax := min (k * k - 1 : ℤ) r_xmax
  let new_ymin := max 0 r_ymin
  let new_ymax := min (k * k - 1 : ℤ) r_ymax
  if h_valid : new_xmin ≤ new_xmax ∧ new_ymin ≤ new_ymax then
    some {
      x_min := new_xmin.toNat
      x_max := new_xmax.toNat
      y_min := new_ymin.toNat
      y_max := new_ymax.toNat
      h_x_le := Int.toNat_le_toNat h_valid.1
      h_y_le := Int.toNat_le_toNat h_valid.2
      h_x_bound := by
        zify; simp; exact ⟨lt_of_le_of_lt (min_le_left _ _) (by omega), NeZero.ne k⟩
      h_y_bound := by
        zify; simp; exact ⟨lt_of_le_of_lt (min_le_left _ _) (by omega), NeZero.ne k⟩
      h_disjoint := by
        intro p hp h_in_rect
        zify at h_in_rect
        obtain ⟨hx1, hx2, hy1, hy2⟩ := h_in_rect
        try zify at hx1 hx2 hy1 hy2
        have h_xmin_nonneg : 0 ≤ new_xmin := le_max_left 0 r_xmin
        have h_ymin_nonneg : 0 ≤ new_ymin := le_max_left 0 r_ymin
        have h_xmax_nonneg : 0 ≤ new_xmax := le_trans h_xmin_nonneg h_valid.1
        have h_ymax_nonneg : 0 ≤ new_ymax := le_trans h_ymin_nonneg h_valid.2
        simp only [Int.toNat_of_nonneg h_xmin_nonneg] at hx1
        simp only [Int.toNat_of_nonneg h_xmax_nonneg] at hx2
        simp only [Int.toNat_of_nonneg h_ymin_nonneg] at hy1
        simp only [Int.toNat_of_nonneg h_ymax_nonneg] at hy2
        have h_wr : in_white_rect k s t p := by
          constructor
          · constructor
            · linarith [le_max_right 0 r_xmin, hx1]
            · linarith [min_le_right (k * k - 1 : ℤ) r_xmax, hx2]
          · constructor
            · linarith [le_max_right 0 r_ymin, hy1]
            · linarith [min_le_right (k * k - 1 : ℤ) r_ymax, hy2]
        have h_in_M := rect_subset_M k s t p hk h_wr
        rw [M_st, mem_filter] at h_in_M
        rcases h_in_M with ⟨_, h_not_black, _⟩
        contradiction
    }
  else
    none

variable (h_00 : M_st k 0 0 = ∅)
variable (h_k0 : M_st k k 0 = ∅)
variable (h_0k : M_st k 0 k = ∅)
variable (h_kk : M_st k k k = ∅)

lemma matilda_upper_bound_sum (k : ℕ) (hk : 2 ≤ k) :
    let kz : ℤ := k
    let range_sq := Finset.Icc 0 kz ×ˢ Finset.Icc 0 kz
    let corners : Finset (ℤ × ℤ) := {(0, 0), (kz, 0), (0, kz), (kz, kz)}
    let valid_indices := range_sq \ corners
    valid_indices.card = k^2 + 2 * k - 3 := by
  intro kz range_sq corners valid_indices
  have h_total : range_sq.card = (k + 1) * (k + 1) := by
    dsimp [range_sq]
    rw [Finset.card_product]
    simp only [Int.card_Icc, sub_zero]
    have : (kz + 1).toNat = k + 1 := by dsimp [kz]
    rw [this]
  have h_corners : corners.card = 4 := by
    dsimp [corners]
    have h_ne : kz ≠ 0 := by dsimp [kz]; omega
    repeat rw [card_insert_of_notMem] <;> try (simp [Prod.mk.injEq]; omega)
    rw [card_singleton]
  have h_subset : corners ⊆ range_sq := by
    intro p hp
    simp only [corners, mem_insert, mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl
    all_goals (
      simp only [range_sq, mem_product, mem_Icc]
      constructor <;> constructor <;> omega
    )
  rw [card_sdiff, inter_eq_left.mpr h_subset]
  rw [h_total, h_corners]
  have h_eq: (k + 1) * (k + 1) = k^2 + 2 * k + 1 := by ring
  rw [h_eq]
  omega

lemma eq_of_modEq_fin {k : ℕ} (_ : 2 ≤ k) {a b : Fin (k * k)}
    (h_equiv : (a : ℤ) ≡ b [ZMOD mod_base k]) : a = b := by
  let M := mod_base k
  have h_bound : (k : ℤ)^2 < M := by dsimp [M, mod_base]; linarith
  rw [Int.modEq_iff_dvd] at h_equiv
  let diff : ℤ := (b : ℤ) - (a : ℤ)
  change M ∣ diff at h_equiv
  have h_diff_zero : diff = 0 := by
    by_contra h_ne
    have h_abs_lt : |diff| < M := by
      rw [abs_sub_lt_iff]
      have ha : (a : ℤ) < k^2 := by rw [pow_two]; exact Int.ofNat_lt.mpr a.isLt
      have hb : (b : ℤ) < k^2 := by rw [pow_two]; exact Int.ofNat_lt.mpr b.isLt
      constructor
      · calc (b : ℤ) - a
          _ < (k:ℤ)^2 - 0 := by linarith [Int.natCast_nonneg b]
          _ < M           := by linarith
      · calc (a : ℤ) - b
          _ < (k:ℤ)^2 - 0 := by linarith [Int.natCast_nonneg a]
          _ < M          := by linarith
    have h_dvd_abs : M ∣ |diff| := by rw [dvd_abs]; exact h_equiv
    have h_le : M ≤ |diff| :=
      Int.le_of_dvd (abs_pos.mpr h_ne) h_dvd_abs
    linarith
  omega

lemma unique_row_all_black (k : ℕ) (hk : 2 ≤ k) :
    ∀ p1 ∈ all_black_k k, ∀ p2 ∈ all_black_k k, px p1 = px p2 → p1 = p2 := by
  intro p1 hp1 p2 hp2 hx
  simp only [all_black_k, mem_filter, beq_iff_eq] at hp1 hp2
  obtain ⟨_, ht1⟩ := hp1
  obtain ⟨_, ht2⟩ := hp2
  let M := mod_base k
  have h_pos : M > 0 := by apply Int.add_pos_of_nonneg_of_pos (sq_nonneg _) (by decide)
  have h_equiv : val_t k p1 ≡ val_t k p2 [ZMOD M] := ht1.2.trans ht2.2.symm
  dsimp [val_t] at h_equiv
  have h_x_eq : (p1.1 : ℤ) = p2.1 := by zify [px] at hx; exact hx
  rw [h_x_eq] at h_equiv
  let C := (k : ℤ) * p2.1 + k^2 + k
  have h_step : (k : ℤ) * p2.1 - p1.2 + k^2 + k = C - p1.2 := by
    dsimp [C]; ring
  have h_step2 : (k : ℤ) * p2.1 - p2.2 + k^2 + k = C - p2.2 := by
    dsimp [C]; ring
  rw [h_step, h_step2] at h_equiv
  rw [sub_eq_add_neg, sub_eq_add_neg] at h_equiv
  have h_neg_y : -(p1.2 : ℤ) ≡ -(p2.2 : ℤ) [ZMOD M] := by
    exact Int.ModEq.add_left_cancel  (Int.ModEq.refl C) h_equiv
  have h_y_equiv : (p1.2 : ℤ) ≡ p2.2 [ZMOD M] := by
    apply Int.ModEq.neg at h_neg_y
    simpa using h_neg_y
  have h_y_eq : p1.2 = p2.2 := eq_of_modEq_fin hk h_y_equiv
  ext; exact hx; rw [h_y_eq]

lemma unique_col_all_black (k : ℕ) (hk : 2 ≤ k) :
    ∀ p1 ∈ all_black_k k, ∀ p2 ∈ all_black_k k, py p1 = py p2 → p1 = p2 := by
  intro p1 hp1 p2 hp2 hy
  simp only [all_black_k, mem_filter, beq_iff_eq] at hp1 hp2
  obtain ⟨_, hs1⟩ := hp1
  obtain ⟨_, hs2⟩ := hp2
  let M := mod_base k
  have h_pos : M > 0 := by apply Int.add_pos_of_nonneg_of_pos (sq_nonneg _) (by decide)
  have h_equiv : val_s k p1 ≡ val_s k p2 [ZMOD M] := hs1.1.trans hs2.1.symm
  dsimp [val_s] at h_equiv
  have h_y_eq : (p1.2 : ℤ) = p2.2 := by zify [py] at hy; exact hy
  rw [h_y_eq] at h_equiv
  let C := (k : ℤ) * p2.2 + k + 1
  have h_step1 : (p1.1 : ℤ) + k * p2.2 + k + 1 = p1.1 + C := by dsimp [C]; ring
  have h_step2 : (p2.1 : ℤ) + k * p2.2 + k + 1 = p2.1 + C := by dsimp [C]; ring
  rw [h_step1, h_step2] at h_equiv
  have h_x_equiv : (p1.1 : ℤ) ≡ p2.1 [ZMOD M] := by exact Int.ModEq.add_right_cancel' C h_equiv
  have h_x_eq : p1.1 = p2.1 := eq_of_modEq_fin hk h_x_equiv
  ext; rw [h_x_eq]; exact hy

theorem card_all_black_le (k : ℕ) (hk : 2 ≤ k) :
    (all_black_k k).card ≤ k * k := by
  nth_rewrite 2 [← Fintype.card_fin (k * k)]
  rw [← card_univ]
  apply card_le_card_of_injOn (fun p => p.1)
  · intro p hp; exact mem_univ p.1
  · intro p1 hp1 p2 hp2 hx
    exact unique_row_all_black k hk p1 hp1 p2 hp2 (congrArg Fin.val hx)

lemma b_st_bounds_valid (k : ℕ) (hk : 2 ≤ k) (s t : ℕ)
    (hs : 1 ≤ s ∧ s ≤ k) (ht : 1 ≤ t ∧ t ≤ k) :
    let b := b_st_coords k s t
    0 ≤ b.1 ∧ b.1 < k * k ∧ 0 ≤ b.2 ∧ b.2 < k * k := by
  dsimp [b_st_coords]
  zify at hs ht hk
  refine ⟨?_,?_, ?_, ?_⟩
  · apply add_nonneg; linarith; apply mul_nonneg <;> linarith
  · calc ((s : ℤ) - 1) + ((t : ℤ) - 1) * k
      _ ≤ (k - 1) + (k - 1) * k := by gcongr <;> omega
      _ = k^2 - 1 := by ring
      _ < k * k := by linarith
  · calc (s : ℤ) * k - t
      _ ≥ 1 * k - k := by gcongr <;> omega
      _ = 0 := by ring
  · calc (s : ℤ) * k - t
      _ ≤ k * k - 1 := by gcongr <;> omega
      _ < k * k := by linarith

theorem card_all_black_ge (k : ℕ) (hk : 2 ≤ k) :
    k * k ≤ (all_black_k k).card := by
  let domain : Finset (Fin k × Fin k) := univ
  let f : (Fin k × Fin k) → Point (k * k) := fun ⟨i, j⟩ =>
    let s := (i.val : ℤ) + 1
    let t := (j.val : ℤ) + 1
    have : s ≤ k ∧ t ≤ k := by omega
    make_b_point k s t (by
      apply b_st_bounds_valid k hk _ _
      · constructor <;> linarith
      · constructor <;> linarith
    )
  have h_card : domain.card = k * k := by
    dsimp [domain]
    rw [Fintype.card_prod, Fintype.card_fin]
  nth_rewrite 1 [← h_card]
  apply Finset.card_le_card_of_injOn f
  · intro ⟨i, j⟩ _
    dsimp [f]
    let s := (i.val : ℤ) + 1
    let t := (j.val : ℤ) + 1
    have : s ≤ k ∧ t ≤ k := by omega
    have h_props := b_st_props k s t (by
       apply b_st_bounds_valid k hk _ _ <;> constructor <;> linarith
    )
    exact h_props.is_black
  · intro ⟨i1, j1⟩ _ ⟨i2, j2⟩ _ h_eq
    dsimp [f] at h_eq
    let s1 := (i1.val : ℤ) + 1; let t1 := (j1.val : ℤ) + 1
    let s2 := (i2.val : ℤ) + 1; let t2 := (j2.val : ℤ) + 1
    have h_ineq: s1 ≤ k ∧ s2 ≤ k ∧ t1 ≤ k ∧ t2 ≤ k := by omega
    have h_prop1 := b_st_props k s1 t1 (by
      apply b_st_bounds_valid k hk _ _ <;> constructor <;> linarith)
    have h_prop2 := b_st_props k s2 t2 (by
      apply b_st_bounds_valid k hk _ _ <;> constructor <;> linarith)
    have h_s_val_eq :
    calc_s k (make_b_point k s1 t1
      (by apply b_st_bounds_valid k hk _ _ <;> constructor <;> linarith))
      = calc_s k (make_b_point k s2 t2
        (by apply b_st_bounds_valid k hk _ _ <;> constructor <;> linarith)) :=
      congrArg (calc_s k) h_eq
    rw [h_prop1.is_s, h_prop2.is_s] at h_s_val_eq
    have h_s_eq : s1 = s2 := h_s_val_eq
    have h_t_val_eq := congrArg (calc_t k) h_eq
    rw [h_prop1.is_t, h_prop2.is_t] at h_t_val_eq
    have h_t_eq : t1 = t2 := h_t_val_eq
    simp [s1, s2, t1, t2] at h_s_eq h_t_eq
    ext
    · simp; exact h_s_eq
    · simp; exact h_t_eq

lemma card_all_black_k_eq_n (k : ℕ) (hk : 2 ≤ k) :
    (all_black_k k).card = k * k :=
  le_antisymm (card_all_black_le k hk) (card_all_black_ge k hk)

noncomputable def construct_partition (k : ℕ) (hk : 2 ≤ k) [NeZero k]
    [DecidableEq (Matilda (k * k) (all_black_k k))] :
    Finset (Matilda (k * k) (all_black_k k)) :=
  let kz : ℤ := k
  haveI : NeZero (k * k) := ⟨Nat.mul_ne_zero NeZero.out NeZero.out⟩
  let valid_indices := (Icc 0 kz ×ˢ Icc 0 kz) \
                       {(0, 0), (kz, 0), (0, kz), (kz, kz)}
  let P_list := valid_indices.toList.filterMap (fun x =>
    match clipped_rect k hk x.1 x.2 with
    | some m => some (cast (by dsimp) m)
    | none => none
  )

  P_list.toFinset

variable {k : ℕ} (hk : 2 ≤ k) [NeZero k]
def f (p : Point (k * k)) : ℤ × ℤ := (calc_s k p, calc_t k p)

lemma mem_M_st_iff_fiber {k : ℕ} {p : Point (k * k)} {s t : ℤ} :
    p ∈ M_st k s t ↔ (f p = (s, t) ∧ p ∉ all_black_k k) := by
  simp [f, M_st]; tauto

lemma mem_matilda_iff_mem_M_st {k : ℕ} {hk : 2 ≤ k} [NeZero k]
    {idx : ℤ × ℤ} {m : Matilda (k * k) (all_black_k k)}
    (h_clipped : clipped_rect k hk idx.1 idx.2 = some m) {p : Point (k * k)} :
    m.mem p ↔ p ∈ M_st k idx.1 idx.2 := by
  simp [M_st, mem_filter, mem_univ, true_and]
  unfold clipped_rect at h_clipped
  simp (config := { zeta := true }) at h_clipped
  obtain ⟨h_valid, h_eq⟩ := h_clipped
  subst h_eq
  simp only [px, py]
  have hx_p : 0 ≤ (p.1 : ℤ) ∧ (p.1 : ℤ) ≤ ↑(k * k) - 1 :=
  ⟨by linarith, by omega⟩
  have hy_p : 0 ≤ (p.2 : ℤ) ∧ (p.2 : ℤ) ≤ ↑(k * k) - 1 :=
  ⟨by linarith, by omega⟩
  zify at *
  simp [hx_p, hy_p] at *
  constructor
  · intro h
    rw [← mem_rect_iff_idx_eq k p idx.1 idx.2 hk]
    simp at h
    simp [rect_finset, in_white_rect]
    rcases h.2.1 with hx_le | hp1_zero
    · constructor
      · constructor
        · exact h.1
        · rcases h.2.1 with hx_le | hp1_zero
          · exact hx_le
          · have : ↑↑p.1 = 0 := by rw [hp1_zero]; simp
            rw [this]; exact h_valid.1.2.1
      · constructor
        · exact h.2.2.1
        · rcases h.2.2.2 with hy_le | hp2_zero
          · exact hy_le
          · have : ↑↑p.2 = 0 := by rw [hp2_zero]; simp
            rw [this]; zify; linarith [h_valid.2.2.1]
    · constructor
      · constructor
        · exact h.1
        · have : ↑↑p.1 = 0 := by rw [hp1_zero]; simp
          linarith [h_valid]
      · constructor
        · exact h.2.2.1
        · rcases h.2.2.2 with hy_le | hp2_zero
          · exact hy_le
          · have : ↑↑p.2 = 0 := by rw [hp2_zero]; simp
            simp [this]; exact h_valid.2.2.1
  · intro h_M
    rw [← mem_rect_iff_idx_eq k p idx.1 idx.2 hk] at h_M
    simp [rect_finset, in_white_rect] at h_M
    constructor
    · exact h_M.1.1
    · constructor
      · left; exact h_M.1.2
      · constructor
        · exact h_M.2.1
        · left; exact h_M.2.2

lemma construction_is_valid_partition (k : ℕ) (hk : 2 ≤ k) [NeZero k]
    [DecidableEq (Matilda (k * k) (all_black_k k))] :
    ∀ p ∉ all_black_k k, ∃! m ∈ construct_partition k hk, m.mem p := by
  intro p hp_white
  let s := calc_s k p; let t := calc_t k p
  have h_range := s_t_range k hk p
  have h_in_M : p ∈ M_st k s t := by
    simp [M_st]; exact ⟨hp_white, rfl, rfl⟩
  let kz : ℤ := k
  have h_pos : 0 < kz * kz - 1 := by
    have h_kk_ge_4 : 4 ≤ k * k := Nat.mul_le_mul hk hk
    linarith
  let valid_indices := (Finset.Icc 0 kz ×ˢ Finset.Icc 0 kz) \ {(0, 0), (kz, 0), (0, kz), (kz, kz)}
  have h_idx_valid : (s, t) ∈ valid_indices := by
    rw [show calc_s k p = s from rfl, show calc_t k p = t from rfl] at h_range
    simp only [valid_indices, mem_sdiff, mem_product, mem_Icc, mem_insert, mem_singleton]
    refine ⟨⟨⟨h_range.1, h_range.2.1⟩, ⟨h_range.2.2.1, h_range.2.2.2⟩⟩, ?_⟩
    intro h_corner
    rcases h_corner with h_eq | h_eq | h_eq | h_eq
    · simp at h_eq; obtain ⟨hs ,ht⟩ := h_eq;
      rw [hs, ht] at h_in_M; rw [M_00_empty k hk] at h_in_M; contradiction
    · simp at h_eq; obtain ⟨hs, ht⟩ := h_eq
      rw [hs, ht] at h_in_M; rw [M_k0_empty k] at h_in_M; contradiction
    · simp at h_eq; obtain ⟨hs, ht⟩ := h_eq
      rw [hs, ht] at h_in_M; rw [M_0k_empty k hk] at h_in_M; contradiction
    · simp at h_eq; obtain ⟨hs, ht⟩ := h_eq
      rw [hs, ht] at  h_in_M; rw [M_kk_empty k hk] at h_in_M; contradiction
  have h_eq_rect := M_st_eq_rect k s t hk
  rw [h_eq_rect] at h_in_M
  have hx_range : 0 ≤ (p.1 : ℤ) ∧ (p.1 : ℤ) ≤ k * k - 1 := by omega
  have hy_range : 0 ≤ (p.2 : ℤ) ∧ (p.2 : ℤ) ≤ k * k - 1 := by omega
  obtain ⟨m_target, h_some, h_mem_p⟩ : ∃ m, clipped_rect k hk s t = some m ∧ m.mem p := by
    unfold clipped_rect
    simp only
    split_ifs with h_valid
    · refine ⟨{ x_min := _, x_max := _, y_min := _, y_max := _, h_x_le := _,
                h_y_le := _, h_x_bound := _, h_y_bound := _, h_disjoint := _ }, rfl, ?_⟩
      simp only [rect_finset, mem_filter, mem_univ, true_and] at h_in_M
      unfold Matilda.mem
      simp only [px, py]
      zify
      simp at *
      repeat (first | constructor | linarith[hx_range, hy_range,
        h_in_M.1.1, h_in_M.1.2, h_in_M.2.1, h_in_M.2.2])
    · exfalso
      simp only [rect_finset, mem_filter, mem_univ, true_and, in_white_rect] at h_in_M
      obtain ⟨⟨hx_low, hx_high⟩, ⟨hy_low, hy_high⟩⟩ := h_in_M

      apply h_valid
      constructor
      · rw [max_le_iff]
        constructor
        · rw [le_min_iff]
          constructor
          · exact le_of_lt h_pos
          · exact le_trans hx_range.1 hx_high
        · rw [le_min_iff]
          constructor
          · exact le_trans hx_low hx_range.2
          · exact le_trans hx_low hx_high
      · rw [max_le_iff]
        constructor
        · rw [le_min_iff]
          constructor
          · nlinarith
          · exact le_trans hy_range.1 hy_high
        · rw [le_min_iff]
          constructor
          · exact le_trans hy_low hy_range.2
          · exact le_trans hy_low hy_high
  exists m_target
  constructor
  · constructor
    · dsimp [construct_partition]
      rw [List.mem_toFinset, List.mem_filterMap]
      exact ⟨(s, t), ⟨mem_toList.mpr h_idx_valid, by simp [h_some]⟩⟩
    · exact h_mem_p
  · intro m' h_cond
    obtain ⟨hm', h_mem_p'⟩ := h_cond
    obtain ⟨idx', ⟨h_idx_valid', h_some'⟩⟩ := by
      dsimp [construct_partition] at hm'
      rw [List.mem_toFinset, List.mem_filterMap] at hm'
      exact hm'
    cases h_res : clipped_rect k hk idx'.1 idx'.2 with
    | none =>
      simp [h_res] at h_some'
    | some m_val =>
      simp [h_res] at h_some'
      rw [h_some'] at h_res
      rw [mem_matilda_iff_mem_M_st h_res] at h_mem_p'
      rw [mem_M_st_iff_fiber] at h_mem_p'
      have h_idx_match : (s, t) = idx' := by
        have h_f_p : f p = (s, t) := rfl
        rw [← h_f_p]
        exact h_mem_p'.left
      rw [← h_idx_match] at h_res
      rw [h_res] at h_some
      injection h_some with h_final

end Construction

theorem matilda_solution_general (k : ℕ) (hk : 2 ≤ k) :
    let n := k * k
    haveI : NeZero n := ⟨by apply mul_ne_zero <;> linarith⟩
    IsMinMatildaCount n (k^2 + 2 * k - 3) := by
  intro n
  let m_ans := k^2 + 2 * k - 3
  haveI : NeZero n := ⟨by
    dsimp [n]
    apply mul_ne_zero <;> linarith [hk]⟩
  dsimp [IsMinMatildaCount]
  constructor
  · intro all_black partition h_valid
    obtain ⟨h_card, h_row, h_col, h_part⟩ := h_valid
    have h_raw := matilda_lower_bound h_card h_row h_col partition h_part
    rw [show n + (4 * n).sqrt - 3 = k^2 + 2 * k - 3 by
      dsimp [n]
      have h_sqrt : (4 * (k * k)).sqrt = 2 * k := by
        have h_eq: 4 * (k * k) = (2 * k) * (2 * k) := by ring
        rw [h_eq, Nat.sqrt_eq]
      rw [h_sqrt]; ring_nf
    ] at h_raw
    exact h_raw
  · haveI : NeZero k := ⟨by linarith⟩
    letI : DecidableEq (Matilda (k * k) (all_black_k k)) := Classical.decEq _
    let P := construct_partition k hk
    exists (all_black_k k), P
    constructor
    · refine ⟨?_, ?_, ?_, ?_⟩
      · exact card_all_black_k_eq_n k hk
      · exact unique_row_all_black k hk
      · exact unique_col_all_black k hk
      · exact construction_is_valid_partition k hk
    · apply le_antisymm
      · dsimp [P]
        rw [construct_partition]
        dsimp
        apply le_trans (List.toFinset_card_le _)
        apply le_trans (List.length_filterMap_le _ _)
        rw [length_toList]
        rw [matilda_upper_bound_sum k hk]
      · have h_valid_P : IsValidConfiguration n (all_black_k k) P := ⟨
          by dsimp [n]; rw [card_all_black_k_eq_n k hk],
          unique_row_all_black k hk,
          unique_col_all_black k hk,
          by dsimp [P]; exact construction_is_valid_partition k hk
        ⟩
        have h_lower := matilda_lower_bound
          h_valid_P.1 h_valid_P.2.1 h_valid_P.2.2.1 P h_valid_P.2.2.2
        rw [show n + (4 * n).sqrt - 3 = k^2 + 2 * k - 3 by
          dsimp [n]
          have h_sqrt : (4 * (k * k)).sqrt = 2 * k := by
            have : 4 * (k * k) = (2 * k) * (2 * k) := by ring
            rw [this, Nat.sqrt_eq]
          rw [h_sqrt]
          ring_nf
        ] at h_lower
        exact h_lower

snip end

determine solution_value : ℕ := 2112

problem imo2025_p6 : IsMinMatildaCount 2025  solution_value := by
  let k := 45
  have h_general := matilda_solution_general k (by norm_num)
  norm_num at h_general
  exact h_general

end Imo2025P6
