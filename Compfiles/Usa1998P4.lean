/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.Order.Bounds.Basic
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# USA Mathematical Olympiad 1998, Problem 4

A computer screen shows a 98 × 98 chessboard, colored in the usual way.
One can select with a mouse any rectangle with sides on the lines of the
chessboard and click the mouse button: as a result, the colors in the
selected rectangle switch (black becomes white, white becomes black).
Find, with proof, the minimum number of mouse clicks needed to make the
chessboard all one color.
-/

namespace Usa1998P4

def chessboard : Type := Fin 98 × Fin 98

def coloring := chessboard → ZMod 2

def all_same_color (f : coloring) : Prop :=
  ∃ c : ZMod 2, ∀ s : chessboard, f s = c

structure Rectangle where
  x : ℕ
  y : ℕ
  width : ℕ
  height : ℕ

def recolor_rect (f : coloring) (r : Rectangle) : coloring :=
  fun ⟨x, y⟩ ↦ if r.x ≤ x.val ∧
                  r.y ≤ y.val ∧
                  x.val < r.x + r.width ∧
                  y.val < r.y + r.height
               then
                  f ⟨x, y⟩ + 1
               else
                  f ⟨x, y⟩

def start_coloring : coloring := fun ⟨x, y⟩ ↦ x.val + y.val

def possible_num_clicks : Set ℕ :=
  { n : ℕ | ∃ rs : List Rectangle,
    (all_same_color (rs.foldl recolor_rect start_coloring) ∧
     rs.length = n) }

determine min_clicks : ℕ := 98

snip begin

def Rectangle.Contains (r : Rectangle) (s : chessboard) : Prop :=
  r.x ≤ s.1.val ∧
  r.y ≤ s.2.val ∧
  s.1.val < r.x + r.width ∧
  s.2.val < r.y + r.height

instance Rectangle.decidableContains (r : Rectangle) (s : chessboard) :
    Decidable (r.Contains s) := by
  unfold Rectangle.Contains
  infer_instance

def colRect (k : ℕ) : Rectangle := ⟨2 * k, 0, 1, 98⟩

def rowRect (k : ℕ) : Rectangle := ⟨0, 2 * k, 98, 1⟩

lemma colRect_contains_iff (k : ℕ) (s : chessboard) :
    (colRect k).Contains s ↔ s.1.val = 2 * k := by
  simp [Rectangle.Contains, colRect]
  omega

lemma rowRect_contains_iff (k : ℕ) (s : chessboard) :
    (rowRect k).Contains s ↔ s.2.val = 2 * k := by
  simp [Rectangle.Contains, rowRect]
  omega

def rectColor (r : Rectangle) : coloring :=
  fun s ↦ if r.Contains s then 1 else 0

lemma recolor_rect_apply (f : coloring) (r : Rectangle) (s : chessboard) :
    recolor_rect f r s = f s + if r.Contains s then 1 else 0 := by
  rcases s with ⟨x, y⟩
  simp only [recolor_rect, Rectangle.Contains]
  split <;> simp

lemma recolor_rect_eq_add_rectColor (f : coloring) (r : Rectangle) :
    recolor_rect f r = fun s ↦ f s + rectColor r s := by
  funext s
  rw [recolor_rect_apply]
  rfl

lemma foldl_recolor_rect_apply (rs : List Rectangle) (f : coloring) (s : chessboard) :
    (rs.foldl recolor_rect f) s =
      f s + (((rs.filter fun r ↦ r.Contains s).length : ZMod 2)) := by
  induction rs generalizing f with
  | nil =>
      simp
  | cons r rs ih =>
      rw [List.foldl_cons, ih, recolor_rect_apply]
      by_cases h : r.Contains s
      · simp [h, add_assoc, add_comm]
      · simp [h]

lemma length_filter_map {α β : Type} (l : List α) (f : α → β) (p : β → Prop)
    [DecidablePred p] :
    ((l.map f).filter p).length = (l.filter fun a ↦ p (f a)).length := by
  simpa using congrArg List.length
    (List.filter_map (l := l) (f := f) (p := fun b ↦ decide (p b)))

lemma evenCoord_filter_length (m : ℕ) (hm : m < 98) :
    ((List.range 49).filter fun k ↦ m = 2 * k).length =
      if Even m then 1 else 0 := by
  by_cases hEven : Even m
  · rw [if_pos hEven]
    obtain ⟨k, hk⟩ := hEven
    have hnodup : ((List.range 49).filter fun j ↦ m = 2 * j).Nodup :=
      List.Nodup.filter _ List.nodup_range
    rw [← List.toFinset_card_of_nodup hnodup]
    have hfin : ((List.range 49).filter fun j ↦ m = 2 * j).toFinset =
        ({k} : Finset ℕ) := by
      ext j
      simp
      omega
    rw [hfin]
    simp
  · rw [if_neg hEven]
    simp only [List.length_eq_zero_iff, List.filter_eq_nil_iff, List.mem_range,
      decide_eq_true_eq]
    intro j _hj h
    exact hEven ⟨j, by omega⟩

lemma filter_cols_length (s : chessboard) :
    (((List.range 49).map colRect).filter fun r ↦ r.Contains s).length =
      if Even s.1.val then 1 else 0 := by
  rw [length_filter_map]
  simp_rw [colRect_contains_iff]
  exact evenCoord_filter_length s.1.val s.1.isLt

lemma filter_rows_length (s : chessboard) :
    (((List.range 49).map rowRect).filter fun r ↦ r.Contains s).length =
      if Even s.2.val then 1 else 0 := by
  rw [length_filter_map]
  simp_rw [rowRect_contains_iff]
  exact evenCoord_filter_length s.2.val s.2.isLt

lemma coord_plus_even_flip (m : ℕ) :
    ((m : ZMod 2) + (if Even m then 1 else 0 : ZMod 2)) = 1 := by
  by_cases hm : Even m
  · have hmz : (m : ZMod 2) = 0 := Even.natCast_zmod_two hm
    simp [hm, hmz]
  · have hodd : Odd m := Nat.not_even_iff_odd.mp hm
    have hmone : (m : ZMod 2) = 1 := Odd.natCast_zmod_two hodd
    simp [hm, hmone]

lemma construction_makes_zero (s : chessboard) :
    (((List.range 49).map colRect ++ (List.range 49).map rowRect).foldl
      recolor_rect start_coloring) s = 0 := by
  rw [foldl_recolor_rect_apply]
  rw [List.filter_append, List.length_append]
  rw [filter_cols_length, filter_rows_length]
  cases s with
  | mk x y =>
      simp only [start_coloring]
      norm_num [Nat.cast_add]
      calc
        (x.val : ZMod 2) + y.val + ((if Even x.val then 1 else 0 : ZMod 2) +
            (if Even y.val then 1 else 0 : ZMod 2))
            = ((x.val : ZMod 2) + (if Even x.val then 1 else 0 : ZMod 2)) +
                ((y.val : ZMod 2) + (if Even y.val then 1 else 0 : ZMod 2)) := by
              ac_rfl
        _ = 1 + 1 := by rw [coord_plus_even_flip, coord_plus_even_flip]
        _ = 0 := by exact CharTwo.add_self_eq_zero (1 : ZMod 2)

abbrev Corner : Type := Fin 99 × Fin 99

-- Extend a coloring by zero outside the board, so every grid-line corner has four formal neighbors.
def cellValue (f : coloring) (x y : ℕ) : ZMod 2 :=
  if hx : x < 98 then
    if hy : y < 98 then
      f (⟨x, hx⟩, ⟨y, hy⟩)
    else
      0
  else
    0

def addColoring (f g : coloring) : coloring :=
  fun s ↦ f s + g s

lemma cellValue_add (f g : coloring) (x y : ℕ) :
    cellValue (addColoring f g) x y = cellValue f x y + cellValue g x y := by
  unfold cellValue addColoring
  split_ifs <;> simp

def maskedCell (p : Prop) [Decidable p] (f : coloring) (x y : ℕ) : ZMod 2 :=
  if p then cellValue f x y else 0

lemma maskedCell_add (p : Prop) [Decidable p] (f g : coloring) (x y : ℕ) :
    maskedCell p (addColoring f g) x y = maskedCell p f x y + maskedCell p g x y := by
  unfold maskedCell
  split <;> simp [cellValue_add]

def cornerDelta (f : coloring) (c : Corner) : ZMod 2 :=
  maskedCell (0 < c.1.val ∧ 0 < c.2.val) f (c.1.val - 1) (c.2.val - 1) +
  maskedCell (c.1.val < 98 ∧ 0 < c.2.val) f c.1.val (c.2.val - 1) +
  maskedCell (0 < c.1.val ∧ c.2.val < 98) f (c.1.val - 1) c.2.val +
  maskedCell (c.1.val < 98 ∧ c.2.val < 98) f c.1.val c.2.val

lemma cornerDelta_add (f g : coloring) (c : Corner) :
    cornerDelta (addColoring f g) c = cornerDelta f c + cornerDelta g c := by
  unfold cornerDelta
  repeat rw [maskedCell_add]
  ac_rfl

def cornerSupport (f : coloring) : Finset Corner :=
  Finset.univ.filter fun c ↦ cornerDelta f c ≠ 0

lemma mem_cornerSupport (f : coloring) (c : Corner) :
    c ∈ cornerSupport f ↔ cornerDelta f c ≠ 0 := by
  simp [cornerSupport]

lemma ne_zero_or_ne_zero_of_add_ne_zero {a b : ZMod 2}
    (h : a + b ≠ 0) : a ≠ 0 ∨ b ≠ 0 := by
  contrapose! h
  simp [h.1, h.2]

lemma cornerSupport_add_subset (f g : coloring) :
    cornerSupport (addColoring f g) ⊆ cornerSupport f ∪ cornerSupport g := by
  intro c
  rw [mem_cornerSupport, cornerDelta_add]
  rw [Finset.mem_union, mem_cornerSupport, mem_cornerSupport]
  exact ne_zero_or_ne_zero_of_add_ne_zero

def inInterval (lo hi x : ℕ) : Prop :=
  lo ≤ x ∧ x < hi

instance inIntervalDecidable (lo hi x : ℕ) : Decidable (inInterval lo hi x) := by
  unfold inInterval
  infer_instance

def boundaryCoord (n : ℕ) : Fin 99 :=
  ⟨min n 98, by omega⟩

-- One-dimensional corner defect for an interval: away from its two boundary
-- coordinates, it is zero.
def axisDelta (lo width : ℕ) (i : Fin 99) : ZMod 2 :=
  (if 0 < i.val then
      if inInterval lo (lo + width) (i.val - 1) then 1 else 0
    else
      0) +
  (if i.val < 98 then
      if inInterval lo (lo + width) i.val then 1 else 0
    else
      0)

lemma inInterval_pred_iff_of_ne_boundary (lo width : ℕ) (i : Fin 99)
    (h0 : 0 < i.val) (h98 : i.val < 98)
    (hlo : i ≠ boundaryCoord lo) (hhi : i ≠ boundaryCoord (lo + width)) :
    inInterval lo (lo + width) (i.val - 1) ↔
      inInterval lo (lo + width) i.val := by
  have hlo_val : i.val ≠ min lo 98 := fun h ↦ hlo (Fin.ext h)
  have hhi_val : i.val ≠ min (lo + width) 98 := fun h ↦ hhi (Fin.ext h)
  unfold inInterval
  constructor
  · intro hleft
    constructor
    · omega
    · by_contra hright
      have hend : i.val = lo + width := by omega
      exact hhi_val (by rw [hend, Nat.min_eq_left (by omega)])
  · intro hright
    constructor
    · by_contra hleft
      have hstart : i.val = lo := by omega
      exact hlo_val (by rw [hstart, Nat.min_eq_left (by omega)])
    · omega

lemma axisDelta_eq_zero_of_ne_boundary (lo width : ℕ) (i : Fin 99)
    (hlo : i ≠ boundaryCoord lo) (hhi : i ≠ boundaryCoord (lo + width)) :
    axisDelta lo width i = 0 := by
  have hlo_val : i.val ≠ min lo 98 := fun h ↦ hlo (Fin.ext h)
  have hhi_val : i.val ≠ min (lo + width) 98 := fun h ↦ hhi (Fin.ext h)
  by_cases h0 : 0 < i.val
  · by_cases h98 : i.val < 98
    · have hsame := inInterval_pred_iff_of_ne_boundary lo width i h0 h98 hlo hhi
      by_cases hright : inInterval lo (lo + width) i.val
      · have hleft : inInterval lo (lo + width) (i.val - 1) := hsame.mpr hright
        simp [axisDelta, h0, h98, hleft, hright, CharTwo.add_self_eq_zero]
      · have hleft : ¬ inInterval lo (lo + width) (i.val - 1) :=
          fun h ↦ hright (hsame.mp h)
        simp [axisDelta, h0, h98, hleft, hright]
    · have hi : i.val = 98 := by omega
      by_cases hleft : inInterval lo (lo + width) (i.val - 1)
      · exfalso
        have hmin : i.val = min (lo + width) 98 := by
          rw [hi, Nat.min_eq_right]
          unfold inInterval at hleft
          omega
        exact hhi_val hmin
      · simp [axisDelta, h0, h98, hleft]
  · have hi : i.val = 0 := Nat.eq_zero_of_not_pos h0
    by_cases hright : inInterval lo (lo + width) i.val
    · exfalso
      have hmin : i.val = min lo 98 := by
        rw [hi]
        unfold inInterval at hright
        have hlo_zero : lo = 0 := by omega
        simp [hlo_zero]
      exact hlo_val hmin
    · simp [axisDelta, h0, hright]

def axisSupport (lo width : ℕ) : Finset (Fin 99) :=
  Finset.univ.filter fun i ↦ axisDelta lo width i ≠ 0

lemma mem_axisSupport (lo width : ℕ) (i : Fin 99) :
    i ∈ axisSupport lo width ↔ axisDelta lo width i ≠ 0 := by
  simp [axisSupport]

lemma axisSupport_subset_boundaries (lo width : ℕ) :
    axisSupport lo width ⊆ {boundaryCoord lo, boundaryCoord (lo + width)} := by
  intro i hi
  rw [mem_axisSupport] at hi
  rw [Finset.mem_insert, Finset.mem_singleton]
  by_contra h
  push Not at h
  exact hi (axisDelta_eq_zero_of_ne_boundary lo width i h.1 h.2)

lemma axisSupport_card_le_two (lo width : ℕ) :
    (axisSupport lo width).card ≤ 2 := by
  calc
    (axisSupport lo width).card ≤ ({boundaryCoord lo, boundaryCoord (lo + width)} :
        Finset (Fin 99)).card := Finset.card_le_card (axisSupport_subset_boundaries lo width)
    _ ≤ 2 := Finset.card_le_two

def axisCellValue (g : Fin 98 → ZMod 2) (x : ℕ) : ZMod 2 :=
  if hx : x < 98 then g ⟨x, hx⟩ else 0

lemma cellValue_mul (gx gy : Fin 98 → ZMod 2) (x y : ℕ) :
    cellValue (fun s ↦ gx s.1 * gy s.2) x y =
      axisCellValue gx x * axisCellValue gy y := by
  unfold cellValue axisCellValue
  split_ifs <;> simp

def maskedAxisCell (p : Prop) [Decidable p] (g : Fin 98 → ZMod 2) (x : ℕ) : ZMod 2 :=
  if p then axisCellValue g x else 0

lemma maskedCell_mul (px py : Prop) [Decidable px] [Decidable py]
    (gx gy : Fin 98 → ZMod 2) (x y : ℕ) :
    maskedCell (px ∧ py) (fun s ↦ gx s.1 * gy s.2) x y =
      maskedAxisCell px gx x * maskedAxisCell py gy y := by
  unfold maskedCell maskedAxisCell
  by_cases hpx : px <;> by_cases hpy : py <;> simp [hpx, hpy, cellValue_mul]

def axisCornerDelta (g : Fin 98 → ZMod 2) (i : Fin 99) : ZMod 2 :=
  maskedAxisCell (0 < i.val) g (i.val - 1) +
  maskedAxisCell (i.val < 98) g i.val

lemma cornerDelta_mul (gx gy : Fin 98 → ZMod 2) (c : Corner) :
    cornerDelta (fun s ↦ gx s.1 * gy s.2) c =
      axisCornerDelta gx c.1 * axisCornerDelta gy c.2 := by
  unfold cornerDelta axisCornerDelta
  repeat rw [maskedCell_mul]
  ring

def intervalMask (lo hi : ℕ) (x : Fin 98) : ZMod 2 :=
  if inInterval lo hi x.val then 1 else 0

def rectXMask (r : Rectangle) : Fin 98 → ZMod 2 :=
  intervalMask r.x (r.x + r.width)

def rectYMask (r : Rectangle) : Fin 98 → ZMod 2 :=
  intervalMask r.y (r.y + r.height)

lemma indicator_and_mul (p q : Prop) [Decidable p] [Decidable q] :
    (if p ∧ q then (1 : ZMod 2) else 0) =
      (if p then 1 else 0) * (if q then 1 else 0) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

lemma rectColor_eq_mul_masks (r : Rectangle) :
    rectColor r = fun s ↦ rectXMask r s.1 * rectYMask r s.2 := by
  funext s
  cases s with
  | mk x y =>
      simp only [rectColor, rectXMask, rectYMask, intervalMask]
      convert indicator_and_mul (inInterval r.x (r.x + r.width) x.val)
          (inInterval r.y (r.y + r.height) y.val) using 1
      simp [Rectangle.Contains, inInterval, and_assoc, and_left_comm]

lemma axisCornerDelta_intervalMask (lo hi : ℕ) (i : Fin 99) :
    axisCornerDelta (intervalMask lo hi) i =
      (if 0 < i.val then
          if inInterval lo hi (i.val - 1) then 1 else 0
        else
          0) +
      (if i.val < 98 then
          if inInterval lo hi i.val then 1 else 0
        else
          0) := by
  unfold axisCornerDelta maskedAxisCell axisCellValue intervalMask
  split_ifs <;> simp_all <;> omega

lemma cornerDelta_rectColor_eq_axisDelta_mul (r : Rectangle) (c : Corner) :
    cornerDelta (rectColor r) c =
      axisDelta r.x r.width c.1 * axisDelta r.y r.height c.2 := by
  rw [rectColor_eq_mul_masks, cornerDelta_mul]
  unfold rectXMask rectYMask axisDelta
  rw [axisCornerDelta_intervalMask, axisCornerDelta_intervalMask]

def rectCornerSupportBound (r : Rectangle) : Finset Corner :=
  (axisSupport r.x r.width).product (axisSupport r.y r.height)

lemma mem_rectCornerSupportBound (r : Rectangle) (c : Corner) :
    c ∈ rectCornerSupportBound r ↔
      axisDelta r.x r.width c.1 ≠ 0 ∧ axisDelta r.y r.height c.2 ≠ 0 := by
  unfold rectCornerSupportBound
  rw [Finset.product_eq_sprod, Finset.mem_product, mem_axisSupport, mem_axisSupport]

lemma cornerSupport_rectColor_subset (r : Rectangle) :
    cornerSupport (rectColor r) ⊆ rectCornerSupportBound r := by
  intro c
  rw [mem_cornerSupport, cornerDelta_rectColor_eq_axisDelta_mul, mem_rectCornerSupportBound]
  exact ne_zero_and_ne_zero_of_mul

lemma cornerSupport_rectColor_card_le_four (r : Rectangle) :
    (cornerSupport (rectColor r)).card ≤ 4 := by
  calc
    (cornerSupport (rectColor r)).card ≤ (rectCornerSupportBound r).card :=
      Finset.card_le_card (cornerSupport_rectColor_subset r)
    _ = (axisSupport r.x r.width).card * (axisSupport r.y r.height).card := by
      unfold rectCornerSupportBound
      simp
    _ ≤ 2 * 2 := Nat.mul_le_mul (axisSupport_card_le_two r.x r.width)
        (axisSupport_card_le_two r.y r.height)
    _ = 4 := by norm_num

lemma zmod_two_add_self (a : ZMod 2) : a + a = 0 := by
  exact CharTwo.add_self_eq_zero a

def rectColorList (rs : List Rectangle) : coloring :=
  fun s ↦ (((rs.filter fun r ↦ r.Contains s).length : ℕ) : ZMod 2)

lemma rectColorList_nil : rectColorList [] = fun _ ↦ 0 := by
  rfl

lemma rectColorList_cons (r : Rectangle) (rs : List Rectangle) :
    rectColorList (r :: rs) = addColoring (rectColor r) (rectColorList rs) := by
  funext s
  unfold rectColorList rectColor addColoring
  by_cases h : r.Contains s
  · simp [h, add_comm]
  · simp [h]

lemma cornerDelta_zero (c : Corner) :
    cornerDelta (fun _ ↦ 0) c = 0 := by
  unfold cornerDelta maskedCell cellValue
  split_ifs <;> simp

lemma cornerSupport_zero :
    cornerSupport (fun _ ↦ 0 : coloring) = ∅ := by
  ext c
  simp [cornerSupport, cornerDelta_zero]

lemma cornerSupport_rectColorList_card_le (rs : List Rectangle) :
    (cornerSupport (rectColorList rs)).card ≤ 4 * rs.length := by
  induction rs with
  | nil =>
      simp [rectColorList_nil, cornerSupport_zero]
  | cons r rs ih =>
      rw [rectColorList_cons]
      calc
        (cornerSupport (addColoring (rectColor r) (rectColorList rs))).card ≤
            (cornerSupport (rectColor r) ∪ cornerSupport (rectColorList rs)).card :=
          Finset.card_le_card (cornerSupport_add_subset (rectColor r) (rectColorList rs))
        _ ≤ (cornerSupport (rectColor r)).card +
            (cornerSupport (rectColorList rs)).card := by
          exact Finset.card_union_le
            (cornerSupport (rectColor r)) (cornerSupport (rectColorList rs))
        _ ≤ 4 + 4 * rs.length := by
          exact Nat.add_le_add (cornerSupport_rectColor_card_le_four r) ih
        _ = 4 * (r :: rs).length := by
          simp
          omega

lemma foldl_recolor_rect_add_start_coloring (rs : List Rectangle) :
    (fun s ↦ (rs.foldl recolor_rect start_coloring) s + start_coloring s) =
      rectColorList rs := by
  funext s
  rw [foldl_recolor_rect_apply]
  unfold rectColorList
  trans (start_coloring s + start_coloring s) +
      (((rs.filter fun r ↦ r.Contains s).length : ℕ) : ZMod 2)
  · ac_rfl
  · simp [zmod_two_add_self]

def constAddStart (c : ZMod 2) : coloring :=
  fun s ↦ c + start_coloring s

-- The checkerboard-to-constant defect count is a boundary count:
-- 388 open-boundary corners plus two board corners.
lemma zmod_two_natCast_four : (4 : ZMod 2) = 0 :=
  Even.natCast_zmod_two (by norm_num : Even 4)

lemma zmod_two_natCast_two : (2 : ZMod 2) = 0 :=
  ZMod.natCast_self 2

lemma zmod_two_natCast_ninety_seven : (97 : ZMod 2) = 1 :=
  Odd.natCast_zmod_two (by norm_num : Odd 97)

lemma zmod_two_natCast_one_ninety_three : (193 : ZMod 2) = 1 :=
  Odd.natCast_zmod_two (by norm_num : Odd 193)

lemma zmod_two_natCast_one_ninety_four : (194 : ZMod 2) = 0 :=
  Even.natCast_zmod_two (by norm_num : Even 194)

lemma cornerDelta_left_open (c : ZMod 2) (y : Fin 99)
    (hy0 : 0 < y.val) (hy98 : y.val < 98) :
    cornerDelta (constAddStart c) ((0 : Fin 99), y) = 1 := by
  unfold cornerDelta maskedCell cellValue constAddStart start_coloring
  have hym : y.val - 1 < 98 := by omega
  simp [hy0, hy98, hym]
  ring_nf
  simp [zmod_two_natCast_two]

lemma cornerDelta_right_open (c : ZMod 2) (y : Fin 99)
    (hy0 : 0 < y.val) (hy98 : y.val < 98) :
    cornerDelta (constAddStart c) ((98 : Fin 99), y) = 1 := by
  unfold cornerDelta maskedCell cellValue constAddStart start_coloring
  have hym : y.val - 1 < 98 := by omega
  simp [hy0, hy98, hym]
  ring_nf
  simp [zmod_two_natCast_two, zmod_two_natCast_one_ninety_three]

lemma cornerDelta_bottom_open (c : ZMod 2) (x : Fin 99)
    (hx0 : 0 < x.val) (hx98 : x.val < 98) :
    cornerDelta (constAddStart c) (x, (0 : Fin 99)) = 1 := by
  unfold cornerDelta maskedCell cellValue constAddStart start_coloring
  have hxm : x.val - 1 < 98 := by omega
  simp [hx0, hx98, hxm]
  ring_nf
  simp [zmod_two_natCast_two]

lemma cornerDelta_top_open (c : ZMod 2) (x : Fin 99)
    (hx0 : 0 < x.val) (hx98 : x.val < 98) :
    cornerDelta (constAddStart c) (x, (98 : Fin 99)) = 1 := by
  unfold cornerDelta maskedCell cellValue constAddStart start_coloring
  have hxm : x.val - 1 < 98 := by omega
  simp [hx0, hx98, hxm]
  ring_nf
  simp [zmod_two_natCast_two, zmod_two_natCast_one_ninety_three]

lemma cornerDelta_interior (c : ZMod 2) (x y : Fin 99)
    (hx0 : 0 < x.val) (hx98 : x.val < 98)
    (hy0 : 0 < y.val) (hy98 : y.val < 98) :
    cornerDelta (constAddStart c) (x, y) = 0 := by
  unfold cornerDelta maskedCell cellValue constAddStart start_coloring
  have hxm : x.val - 1 < 98 := by omega
  have hym : y.val - 1 < 98 := by omega
  simp [hx0, hx98, hy0, hy98, hxm, hym]
  ring_nf
  simp [zmod_two_natCast_four]

lemma cornerDelta_bottom_left (c : ZMod 2) :
    cornerDelta (constAddStart c) ((0 : Fin 99), (0 : Fin 99)) = c := by
  unfold cornerDelta maskedCell cellValue constAddStart start_coloring
  simp

lemma cornerDelta_top_left (c : ZMod 2) :
    cornerDelta (constAddStart c) ((0 : Fin 99), (98 : Fin 99)) = c + 1 := by
  unfold cornerDelta maskedCell cellValue constAddStart start_coloring
  simp
  ring_nf
  rw [zmod_two_natCast_ninety_seven]

lemma cornerDelta_bottom_right (c : ZMod 2) :
    cornerDelta (constAddStart c) ((98 : Fin 99), (0 : Fin 99)) = c + 1 := by
  unfold cornerDelta maskedCell cellValue constAddStart start_coloring
  simp
  ring_nf
  rw [zmod_two_natCast_ninety_seven]

lemma cornerDelta_top_right (c : ZMod 2) :
    cornerDelta (constAddStart c) ((98 : Fin 99), (98 : Fin 99)) = c := by
  unfold cornerDelta maskedCell cellValue constAddStart start_coloring
  simp
  ring_nf
  rw [zmod_two_natCast_one_ninety_four]

def innerCoord (i : Fin 97) : Fin 99 :=
  ⟨i.val + 1, by omega⟩

def innerCoords : Finset (Fin 99) :=
  (Finset.univ : Finset (Fin 97)).image innerCoord

lemma innerCoord_injective : Function.Injective innerCoord := by
  intro a b h
  exact Fin.ext (by simpa [innerCoord] using congrArg Fin.val h)

lemma innerCoords_card : innerCoords.card = 97 := by
  unfold innerCoords
  rw [Finset.card_image_of_injective _ innerCoord_injective]
  simp

lemma mem_innerCoords (i : Fin 99) :
    i ∈ innerCoords ↔ 0 < i.val ∧ i.val < 98 := by
  simp only [innerCoords, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨Nat.succ_pos j.val, Nat.succ_lt_succ j.2⟩
  · intro h
    refine ⟨⟨i.val - 1, by omega⟩, ?_⟩
    exact Fin.ext (by simp [innerCoord]; omega)

def edgeCoords : Finset (Fin 99) :=
  {(0 : Fin 99), (98 : Fin 99)}

lemma edgeCoords_card : edgeCoords.card = 2 := by
  simp [edgeCoords]

lemma mem_edgeCoords (i : Fin 99) :
    i ∈ edgeCoords ↔ i.val = 0 ∨ i.val = 98 := by
  simp only [edgeCoords, Finset.mem_insert, Finset.mem_singleton]
  constructor <;> rintro (h | h)
  · exact Or.inl (congrArg Fin.val h)
  · exact Or.inr (congrArg Fin.val h)
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Fin.ext h)

def verticalOpenBoundary : Finset Corner :=
  edgeCoords.product innerCoords

def horizontalOpenBoundary : Finset Corner :=
  innerCoords.product edgeCoords

def openBoundary : Finset Corner :=
  verticalOpenBoundary ∪ horizontalOpenBoundary

lemma mem_verticalOpenBoundary (p : Corner) :
    p ∈ verticalOpenBoundary ↔
      (p.1.val = 0 ∨ p.1.val = 98) ∧ 0 < p.2.val ∧ p.2.val < 98 := by
  unfold verticalOpenBoundary
  simp [Finset.mem_product, mem_edgeCoords, mem_innerCoords]

lemma mem_horizontalOpenBoundary (p : Corner) :
    p ∈ horizontalOpenBoundary ↔
      (0 < p.1.val ∧ p.1.val < 98) ∧ (p.2.val = 0 ∨ p.2.val = 98) := by
  unfold horizontalOpenBoundary
  simp [Finset.mem_product, mem_edgeCoords, mem_innerCoords]

lemma mem_openBoundary (p : Corner) :
    p ∈ openBoundary ↔
      ((p.1.val = 0 ∨ p.1.val = 98) ∧ 0 < p.2.val ∧ p.2.val < 98) ∨
      ((0 < p.1.val ∧ p.1.val < 98) ∧ (p.2.val = 0 ∨ p.2.val = 98)) := by
  unfold openBoundary
  simp [mem_verticalOpenBoundary, mem_horizontalOpenBoundary]

lemma verticalOpenBoundary_card : verticalOpenBoundary.card = 194 := by
  unfold verticalOpenBoundary
  simp [edgeCoords_card, innerCoords_card]

lemma horizontalOpenBoundary_card : horizontalOpenBoundary.card = 194 := by
  unfold horizontalOpenBoundary
  simp [edgeCoords_card, innerCoords_card]

lemma not_edge_and_inner_coord {i : Fin 99}
    (hEdge : i.val = 0 ∨ i.val = 98) (hInner : 0 < i.val ∧ i.val < 98) :
    False := by
  rcases hEdge with hi | hi <;> omega

lemma edgeCoords_disjoint_innerCoords : Disjoint edgeCoords innerCoords := by
  rw [Finset.disjoint_left]
  intro i hiEdge hiInner
  exact not_edge_and_inner_coord ((mem_edgeCoords i).mp hiEdge) ((mem_innerCoords i).mp hiInner)

lemma verticalOpenBoundary_disjoint_horizontalOpenBoundary :
    Disjoint verticalOpenBoundary horizontalOpenBoundary := by
  unfold verticalOpenBoundary horizontalOpenBoundary
  exact Finset.disjoint_product.mpr (Or.inl edgeCoords_disjoint_innerCoords)

lemma openBoundary_card : openBoundary.card = 388 := by
  unfold openBoundary
  rw [Finset.card_union_of_disjoint verticalOpenBoundary_disjoint_horizontalOpenBoundary]
  rw [verticalOpenBoundary_card, horizontalOpenBoundary_card]

def sameBoardCorners : Finset Corner :=
  {((0 : Fin 99), (0 : Fin 99)), ((98 : Fin 99), (98 : Fin 99))}

def oppositeBoardCorners : Finset Corner :=
  {((0 : Fin 99), (98 : Fin 99)), ((98 : Fin 99), (0 : Fin 99))}

lemma sameBoardCorners_card : sameBoardCorners.card = 2 := by
  simp [sameBoardCorners]

lemma oppositeBoardCorners_card : oppositeBoardCorners.card = 2 := by
  simp [oppositeBoardCorners]

lemma mem_sameBoardCorners (p : Corner) :
    p ∈ sameBoardCorners ↔
      p = ((0 : Fin 99), (0 : Fin 99)) ∨
        p = ((98 : Fin 99), (98 : Fin 99)) := by
  simp [sameBoardCorners]

lemma mem_oppositeBoardCorners (p : Corner) :
    p ∈ oppositeBoardCorners ↔
      p = ((0 : Fin 99), (98 : Fin 99)) ∨
        p = ((98 : Fin 99), (0 : Fin 99)) := by
  simp [oppositeBoardCorners]

lemma fin99_boundary_or_inner (i : Fin 99) :
    i = (0 : Fin 99) ∨ i = (98 : Fin 99) ∨ (0 < i.val ∧ i.val < 98) := by
  have h : i.val = 0 ∨ i.val = 98 ∨ (0 < i.val ∧ i.val < 98) := by
    omega
  rcases h with h | h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Or.inl (Fin.ext h))
  · exact Or.inr (Or.inr h)

lemma sameBoardCorner_not_mem_openBoundary (p : Corner)
    (hp : p ∈ sameBoardCorners) : p ∉ openBoundary := by
  rw [mem_sameBoardCorners] at hp
  rw [mem_openBoundary]
  rcases hp with rfl | rfl <;> simp

lemma openBoundary_disjoint_sameBoardCorners :
    Disjoint openBoundary sameBoardCorners := by
  rw [Finset.disjoint_right]
  exact sameBoardCorner_not_mem_openBoundary

lemma oppositeBoardCorner_not_mem_openBoundary (p : Corner)
    (hp : p ∈ oppositeBoardCorners) : p ∉ openBoundary := by
  rw [mem_oppositeBoardCorners] at hp
  rw [mem_openBoundary]
  rcases hp with rfl | rfl <;> simp

lemma openBoundary_disjoint_oppositeBoardCorners :
    Disjoint openBoundary oppositeBoardCorners := by
  rw [Finset.disjoint_right]
  exact oppositeBoardCorner_not_mem_openBoundary

lemma mem_cornerSupport_constAddStart (c : ZMod 2) (p : Corner) :
    p ∈ cornerSupport (constAddStart c) ↔
      p ∈ openBoundary ∨
        (p ∈ sameBoardCorners ∧ c ≠ 0) ∨
        (p ∈ oppositeBoardCorners ∧ c + 1 ≠ 0) := by
  cases p with
  | mk x y =>
      rw [mem_cornerSupport, mem_openBoundary, mem_sameBoardCorners, mem_oppositeBoardCorners]
      rcases fin99_boundary_or_inner x with hx0 | hx98 | hxmid <;>
        rcases fin99_boundary_or_inner y with hy0 | hy98 | hymid
      · subst x
        subst y
        simp [cornerDelta_bottom_left]
      · subst x
        subst y
        simp [cornerDelta_top_left]
      · subst x
        simp [cornerDelta_left_open, hymid.1, hymid.2]
      · subst x
        subst y
        simp [cornerDelta_bottom_right]
      · subst x
        subst y
        simp [cornerDelta_top_right]
      · subst x
        simp [cornerDelta_right_open, hymid.1, hymid.2]
      · subst y
        simp [cornerDelta_bottom_open, hxmid.1, hxmid.2]
      · subst y
        simp [cornerDelta_top_open, hxmid.1, hxmid.2]
      · have hxne0 : x.val ≠ 0 := by omega
        have hxne98 : x.val ≠ 98 := by omega
        have hyne0 : y.val ≠ 0 := by omega
        have hyne98 : y.val ≠ 98 := by omega
        simp [cornerDelta_interior, hxmid.1, hxmid.2, hymid.1, hymid.2,
          hxne0, hxne98, hyne0, hyne98, Fin.ext_iff]

lemma cornerSupport_zero_add_start_coloring_eq :
    cornerSupport (constAddStart 0) = openBoundary ∪ oppositeBoardCorners := by
  ext p
  rw [mem_cornerSupport_constAddStart, Finset.mem_union]
  simp

lemma cornerSupport_one_add_start_coloring_eq :
    cornerSupport (constAddStart 1) = openBoundary ∪ sameBoardCorners := by
  ext p
  rw [mem_cornerSupport_constAddStart, Finset.mem_union]
  simp [zmod_two_add_self]

lemma cornerSupport_zero_add_start_coloring_card :
    (cornerSupport (constAddStart 0)).card = 390 := by
  rw [cornerSupport_zero_add_start_coloring_eq]
  rw [Finset.card_union_of_disjoint openBoundary_disjoint_oppositeBoardCorners]
  rw [openBoundary_card, oppositeBoardCorners_card]

lemma cornerSupport_one_add_start_coloring_card :
    (cornerSupport (constAddStart 1)).card = 390 := by
  rw [cornerSupport_one_add_start_coloring_eq]
  rw [Finset.card_union_of_disjoint openBoundary_disjoint_sameBoardCorners]
  rw [openBoundary_card, sameBoardCorners_card]

lemma cornerSupport_const_add_start_coloring_card (c : ZMod 2) :
    (cornerSupport (fun s ↦ c + start_coloring s)).card = 390 := by
  change (cornerSupport (constAddStart c)).card = 390
  fin_cases c
  · exact cornerSupport_zero_add_start_coloring_card
  · exact cornerSupport_one_add_start_coloring_card

snip end

problem usa1998_p4 : IsLeast possible_num_clicks min_clicks := by
  constructor
  · use (List.range 49).map colRect ++ (List.range 49).map rowRect
    constructor
    · use 0
      intro s
      exact construction_makes_zero s
    · simp only [List.length_append, List.length_map, List.length_range]
  · rw [mem_lowerBounds]
    intro n hn
    obtain ⟨rs, hrs, hrsl⟩ := hn
    obtain ⟨c, hc⟩ := hrs
    let diff : coloring :=
      fun s ↦ (rs.foldl recolor_rect start_coloring) s + start_coloring s
    have hupper : (cornerSupport diff).card ≤ 4 * rs.length := by
      dsimp [diff]
      rw [foldl_recolor_rect_add_start_coloring]
      exact cornerSupport_rectColorList_card_le rs
    have hsame : diff = fun s ↦ c + start_coloring s := by
      funext s
      dsimp [diff]
      rw [hc s]
    have hlower : 390 ≤ (cornerSupport diff).card := by
      rw [hsame, cornerSupport_const_add_start_coloring_card]
    have hcount : 390 ≤ 4 * rs.length := le_trans hlower hupper
    rw [hrsl] at hcount
    change 98 ≤ n
    omega

end Usa1998P4
