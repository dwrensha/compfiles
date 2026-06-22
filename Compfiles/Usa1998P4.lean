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

/-
Each click adds (mod 2) the indicator function of a rectangle to the
coloring, so the indicators of the clicked rectangles must sum to
`start_coloring + const c`.

To bound the number of clicks from below, associate to each coloring `f`
the function on the 99 × 99 grid-line corners sending a corner to the sum
of the values of the (up to four) cells touching it. This "corner delta"
is additive, and the corner delta of a rectangle indicator is supported
on at most 4 corners (the rectangle's corners). On the other hand the
corner delta of `start_coloring + const c` vanishes only at the
97 × 97 interior corners and at 2 of the 4 board corners, so its support
has at least 99² - 97² - 2 = 390 corners. Hence 4 · (number of clicks)
≥ 390, and at least 98 clicks are needed. A construction with 49 column
rectangles and 49 row rectangles achieves 98.
-/

/-! ### Clicking adds rectangle indicators -/

/-- The indicator coloring of a rectangle. -/
def rectColor (r : Rectangle) : coloring :=
  fun s ↦ if r.x ≤ s.1.val ∧ r.y ≤ s.2.val ∧
             s.1.val < r.x + r.width ∧ s.2.val < r.y + r.height
          then 1 else 0

lemma recolor_rect_apply (f : coloring) (r : Rectangle) (s : chessboard) :
    recolor_rect f r s = f s + rectColor r s := by
  obtain ⟨x, y⟩ := s
  unfold recolor_rect rectColor
  dsimp only
  split_ifs <;> simp

lemma foldl_recolor_apply (rs : List Rectangle) (f : coloring) (s : chessboard) :
    rs.foldl recolor_rect f s = f s + (rs.map (fun r ↦ rectColor r s)).sum := by
  induction rs generalizing f with
  | nil => simp
  | cons r rs ih =>
    rw [List.foldl_cons, ih, List.map_cons, List.sum_cons, recolor_rect_apply]
    ring

/-! ### Corner deltas -/

abbrev Corner : Type := Fin 99 × Fin 99

/-- Extend a coloring by zero outside the board. -/
def cellValue (f : coloring) (x y : ℕ) : ZMod 2 :=
  if hx : x < 98 then
    if hy : y < 98 then
      f (⟨x, hx⟩, ⟨y, hy⟩)
    else 0
  else 0

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

/-- The sum of the values of the four cells touching a grid-line corner. -/
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

/-! ### The corner delta of a rectangle is supported on its 4 corners -/

def clip (n : ℕ) : Fin 99 := ⟨min n 98, Nat.lt_succ_of_le (Nat.min_le_right n 98)⟩

lemma maskedCell_rectColor (m : Prop) [Decidable m] (r : Rectangle) (x y : ℕ) :
    maskedCell m (rectColor r) x y =
      if m ∧ x < 98 ∧ y < 98 ∧
         (r.x ≤ x ∧ r.y ≤ y ∧ x < r.x + r.width ∧ y < r.y + r.height)
      then 1 else 0 := by
  unfold maskedCell cellValue rectColor
  split_ifs <;> tauto

lemma cornerDelta_rectColor_eq_zero_x (r : Rectangle) (p : Corner)
    (h1 : p.1.val ≠ min r.x 98) (h2 : p.1.val ≠ min (r.x + r.width) 98) :
    cornerDelta (rectColor r) p = 0 := by
  obtain ⟨i, j⟩ := p
  have hi := i.isLt
  have hj := j.isLt
  dsimp only at h1 h2 ⊢
  unfold cornerDelta
  dsimp only
  rw [maskedCell_rectColor, maskedCell_rectColor, maskedCell_rectColor,
      maskedCell_rectColor]
  -- in each row, the two cells are either both inside or both outside,
  -- so the four indicator terms cancel in pairs
  have hAB : (((0 < i.val ∧ 0 < j.val) ∧ i.val - 1 < 98 ∧ j.val - 1 < 98 ∧
        (r.x ≤ i.val - 1 ∧ r.y ≤ j.val - 1 ∧ i.val - 1 < r.x + r.width ∧
         j.val - 1 < r.y + r.height)) ↔
      ((i.val < 98 ∧ 0 < j.val) ∧ i.val < 98 ∧ j.val - 1 < 98 ∧
        (r.x ≤ i.val ∧ r.y ≤ j.val - 1 ∧ i.val < r.x + r.width ∧
         j.val - 1 < r.y + r.height))) := by omega
  have hCD : (((0 < i.val ∧ j.val < 98) ∧ i.val - 1 < 98 ∧ j.val < 98 ∧
        (r.x ≤ i.val - 1 ∧ r.y ≤ j.val ∧ i.val - 1 < r.x + r.width ∧
         j.val < r.y + r.height)) ↔
      ((i.val < 98 ∧ j.val < 98) ∧ i.val < 98 ∧ j.val < 98 ∧
        (r.x ≤ i.val ∧ r.y ≤ j.val ∧ i.val < r.x + r.width ∧
         j.val < r.y + r.height))) := by omega
  rw [if_congr hAB rfl rfl, if_congr hCD rfl rfl]
  exact (by decide : ∀ a b : ZMod 2, a + a + b + b = 0) _ _

lemma cornerDelta_rectColor_eq_zero_y (r : Rectangle) (p : Corner)
    (h1 : p.2.val ≠ min r.y 98) (h2 : p.2.val ≠ min (r.y + r.height) 98) :
    cornerDelta (rectColor r) p = 0 := by
  obtain ⟨i, j⟩ := p
  have hi := i.isLt
  have hj := j.isLt
  dsimp only at h1 h2 ⊢
  unfold cornerDelta
  dsimp only
  rw [maskedCell_rectColor, maskedCell_rectColor, maskedCell_rectColor,
      maskedCell_rectColor]
  -- in each column, the two cells are either both inside or both outside
  have hAC : (((0 < i.val ∧ 0 < j.val) ∧ i.val - 1 < 98 ∧ j.val - 1 < 98 ∧
        (r.x ≤ i.val - 1 ∧ r.y ≤ j.val - 1 ∧ i.val - 1 < r.x + r.width ∧
         j.val - 1 < r.y + r.height)) ↔
      ((0 < i.val ∧ j.val < 98) ∧ i.val - 1 < 98 ∧ j.val < 98 ∧
        (r.x ≤ i.val - 1 ∧ r.y ≤ j.val ∧ i.val - 1 < r.x + r.width ∧
         j.val < r.y + r.height))) := by omega
  have hBD : (((i.val < 98 ∧ 0 < j.val) ∧ i.val < 98 ∧ j.val - 1 < 98 ∧
        (r.x ≤ i.val ∧ r.y ≤ j.val - 1 ∧ i.val < r.x + r.width ∧
         j.val - 1 < r.y + r.height)) ↔
      ((i.val < 98 ∧ j.val < 98) ∧ i.val < 98 ∧ j.val < 98 ∧
        (r.x ≤ i.val ∧ r.y ≤ j.val ∧ i.val < r.x + r.width ∧
         j.val < r.y + r.height))) := by omega
  rw [if_congr hAC rfl rfl, if_congr hBD rfl rfl]
  exact (by decide : ∀ a b : ZMod 2, a + b + a + b = 0) _ _

lemma cornerSupport_rectColor_card_le (r : Rectangle) :
    (cornerSupport (rectColor r)).card ≤ 4 := by
  have hsub : cornerSupport (rectColor r) ⊆
      ({clip r.x, clip (r.x + r.width)} : Finset (Fin 99)) ×ˢ
      ({clip r.y, clip (r.y + r.height)} : Finset (Fin 99)) := by
    intro p
    rw [mem_cornerSupport, Finset.mem_product, Finset.mem_insert, Finset.mem_singleton,
        Finset.mem_insert, Finset.mem_singleton]
    intro hp
    constructor
    · by_contra hcon
      push Not at hcon
      exact hp (cornerDelta_rectColor_eq_zero_x r p
        (fun h ↦ hcon.1 (Fin.ext h)) (fun h ↦ hcon.2 (Fin.ext h)))
    · by_contra hcon
      push Not at hcon
      exact hp (cornerDelta_rectColor_eq_zero_y r p
        (fun h ↦ hcon.1 (Fin.ext h)) (fun h ↦ hcon.2 (Fin.ext h)))
  calc (cornerSupport (rectColor r)).card
      ≤ _ := Finset.card_le_card hsub
    _ ≤ 2 * 2 := by
        rw [Finset.card_product]
        exact Nat.mul_le_mul
          ((Finset.card_insert_le _ _).trans
            (le_of_eq (by rw [Finset.card_singleton])))
          ((Finset.card_insert_le _ _).trans
            (le_of_eq (by rw [Finset.card_singleton])))

lemma cornerSupport_zero : cornerSupport (fun _ ↦ 0) = ∅ := by
  ext c
  rw [mem_cornerSupport]
  simp [cornerDelta, maskedCell, cellValue]

lemma cornerSupport_listSum_card_le (rs : List Rectangle) :
    (cornerSupport (fun s ↦ (rs.map (fun r ↦ rectColor r s)).sum)).card
      ≤ 4 * rs.length := by
  induction rs with
  | nil => simp [cornerSupport_zero]
  | cons r rs ih =>
    have heq : (fun s ↦ (((r :: rs).map (fun r ↦ rectColor r s)).sum))
        = addColoring (rectColor r) (fun s ↦ (rs.map (fun r ↦ rectColor r s)).sum) := by
      funext s
      simp [addColoring]
    rw [heq]
    calc (cornerSupport (addColoring (rectColor r)
            (fun s ↦ (rs.map (fun r ↦ rectColor r s)).sum))).card
        ≤ (cornerSupport (rectColor r) ∪
            cornerSupport (fun s ↦ (rs.map (fun r ↦ rectColor r s)).sum)).card :=
          Finset.card_le_card (cornerSupport_add_subset _ _)
      _ ≤ _ := Finset.card_union_le _ _
      _ ≤ 4 + 4 * rs.length :=
          Nat.add_le_add (cornerSupport_rectColor_card_le r) ih
      _ = 4 * (r :: rs).length := by rw [List.length_cons]; ring

/-! ### The corner delta of the target has large support -/

def constAddStart (c : ZMod 2) : coloring := fun s ↦ c + start_coloring s

lemma maskedCell_constAddStart (c : ZMod 2) (m : Prop) [Decidable m] (x y : ℕ) :
    maskedCell m (constAddStart c) x y =
      if m ∧ x < 98 ∧ y < 98 then c + (x : ZMod 2) + (y : ZMod 2) else 0 := by
  unfold maskedCell cellValue
  split_ifs <;> first
    | rfl
    | tauto
    | (simp only [constAddStart, start_coloring]; ring)

def inner : Finset (Fin 99) := Finset.Icc ⟨1, by norm_num⟩ ⟨97, by norm_num⟩

lemma inner_card : inner.card = 97 := by
  rw [inner, Fin.card_Icc]
  rfl

lemma mem_inner (i : Fin 99) : i ∈ inner ↔ 0 < i.val ∧ i.val < 98 := by
  rw [inner, Finset.mem_Icc, Fin.le_def, Fin.le_def]
  exact ⟨fun h ↦ by lia, fun h ↦ by lia⟩

/-- The two board corners where the corner delta of `constAddStart c`
vanishes. -/
def quietCorners (c : ZMod 2) : Finset Corner :=
  if c = 0 then {(⟨0, by norm_num⟩, ⟨0, by norm_num⟩), (⟨98, by norm_num⟩, ⟨98, by norm_num⟩)}
  else {(⟨0, by norm_num⟩, ⟨98, by norm_num⟩), (⟨98, by norm_num⟩, ⟨0, by norm_num⟩)}

lemma quietCorners_card (c : ZMod 2) : (quietCorners c).card ≤ 2 := by
  unfold quietCorners
  split_ifs <;>
    exact (Finset.card_insert_le _ _).trans (le_of_eq (by rw [Finset.card_singleton]))

lemma quiet_subset (c : ZMod 2) :
    Finset.univ.filter (fun p ↦ ¬ (cornerDelta (constAddStart c) p ≠ 0)) ⊆
      (inner ×ˢ inner) ∪ quietCorners c := by
  have hc01 : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  intro p
  rw [Finset.mem_filter, not_not, Finset.mem_union, Finset.mem_product,
      mem_inner, mem_inner]
  intro hp
  replace hp := hp.2
  obtain ⟨i, j⟩ := p
  have hi := i.isLt
  have hj := j.isLt
  unfold cornerDelta at hp
  dsimp only at hp ⊢
  rw [maskedCell_constAddStart, maskedCell_constAddStart, maskedCell_constAddStart,
      maskedCell_constAddStart] at hp
  split_ifs at hp with hA hB hC hD
  -- 16 sign patterns for the four masked cells; each determines the
  -- position of the corner on the board.
  all_goals try (exfalso; omega)
  -- interior: 0 < i < 98, 0 < j < 98
  · exact Or.inl ⟨⟨hA.1.1, hB.1.1⟩, hA.1.2, hC.1.2⟩
  -- top edge: 0 < i < 98, j = 98
  · exfalso
    have hodd : ((i.val - 1 + i.val : ℕ) : ZMod 2) = 0 := by
      push_cast
      linear_combination hp - CharTwo.add_self_eq_zero c
        - CharTwo.add_self_eq_zero ((j.val - 1 : ℕ) : ZMod 2)
    rw [ZMod.natCast_eq_zero_iff_even, Nat.even_iff] at hodd
    omega
  -- right edge: i = 98, 0 < j < 98
  · exfalso
    have hodd : ((j.val - 1 + j.val : ℕ) : ZMod 2) = 0 := by
      push_cast
      linear_combination hp - CharTwo.add_self_eq_zero c
        - CharTwo.add_self_eq_zero ((i.val - 1 : ℕ) : ZMod 2)
    rw [ZMod.natCast_eq_zero_iff_even, Nat.even_iff] at hodd
    omega
  -- corner (98, 98)
  · have hi98 : i.val = 98 := by omega
    have hj98 : j.val = 98 := by omega
    rw [hi98, hj98] at hp
    right
    rw [show i = ⟨98, by norm_num⟩ from Fin.ext hi98,
        show j = ⟨98, by norm_num⟩ from Fin.ext hj98]
    rcases hc01 c with hc | hc <;> subst hc
    · rw [quietCorners, if_pos rfl]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    · exact absurd hp (by decide)
  -- left edge: i = 0, 0 < j < 98
  · exfalso
    have hodd : ((j.val - 1 + j.val : ℕ) : ZMod 2) = 0 := by
      push_cast
      linear_combination hp - CharTwo.add_self_eq_zero c
        - CharTwo.add_self_eq_zero ((i.val : ℕ) : ZMod 2)
    rw [ZMod.natCast_eq_zero_iff_even, Nat.even_iff] at hodd
    omega
  -- corner (0, 98)
  · have hi0 : i.val = 0 := by omega
    have hj98 : j.val = 98 := by omega
    rw [hi0, hj98] at hp
    right
    rw [show i = ⟨0, by norm_num⟩ from Fin.ext hi0,
        show j = ⟨98, by norm_num⟩ from Fin.ext hj98]
    rcases hc01 c with hc | hc <;> subst hc
    · exact absurd hp (by decide)
    · rw [quietCorners, if_neg (by decide)]
      exact Finset.mem_insert_self _ _
  -- bottom edge: 0 < i < 98, j = 0
  · exfalso
    have hodd : ((i.val - 1 + i.val : ℕ) : ZMod 2) = 0 := by
      push_cast
      linear_combination hp - CharTwo.add_self_eq_zero c
        - CharTwo.add_self_eq_zero ((j.val : ℕ) : ZMod 2)
    rw [ZMod.natCast_eq_zero_iff_even, Nat.even_iff] at hodd
    omega
  -- corner (98, 0)
  · have hi98 : i.val = 98 := by omega
    have hj0 : j.val = 0 := by omega
    rw [hi98, hj0] at hp
    right
    rw [show i = ⟨98, by norm_num⟩ from Fin.ext hi98,
        show j = ⟨0, by norm_num⟩ from Fin.ext hj0]
    rcases hc01 c with hc | hc <;> subst hc
    · exact absurd hp (by decide)
    · rw [quietCorners, if_neg (by decide)]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  -- corner (0, 0)
  · have hi0 : i.val = 0 := by omega
    have hj0 : j.val = 0 := by omega
    rw [hi0, hj0] at hp
    right
    rw [show i = ⟨0, by norm_num⟩ from Fin.ext hi0,
        show j = ⟨0, by norm_num⟩ from Fin.ext hj0]
    rcases hc01 c with hc | hc <;> subst hc
    · rw [quietCorners, if_pos rfl]
      exact Finset.mem_insert_self _ _
    · exact absurd hp (by decide)

lemma target_support_card (c : ZMod 2) :
    390 ≤ (cornerSupport (constAddStart c)).card := by
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset Corner))
    (fun p ↦ cornerDelta (constAddStart c) p ≠ 0)
  have hq : (Finset.univ.filter
      (fun p ↦ ¬ (cornerDelta (constAddStart c) p ≠ 0))).card ≤ 9411 := by
    calc (Finset.univ.filter (fun p ↦ ¬ (cornerDelta (constAddStart c) p ≠ 0))).card
        ≤ ((inner ×ˢ inner) ∪ quietCorners c).card :=
          Finset.card_le_card (quiet_subset c)
      _ ≤ (inner ×ˢ inner).card + (quietCorners c).card := Finset.card_union_le _ _
      _ ≤ 9411 := by
          rw [Finset.card_product, inner_card]
          have := quietCorners_card c
          lia
  have huniv : (Finset.univ : Finset Corner).card = 9801 := by
    rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
  rw [huniv] at hsplit
  have : cornerSupport (constAddStart c)
      = Finset.univ.filter (fun p ↦ cornerDelta (constAddStart c) p ≠ 0) := rfl
  rw [this]
  lia

/-! ### The construction -/

def colRect (k : ℕ) : Rectangle := ⟨2 * k, 0, 1, 98⟩

def rowRect (k : ℕ) : Rectangle := ⟨0, 2 * k, 98, 1⟩

lemma rectColor_colRect (k : ℕ) (x y : Fin 98) :
    rectColor (colRect k) (x, y) = if x.val = 2 * k then 1 else 0 := by
  have hy := y.isLt
  unfold rectColor colRect
  dsimp only
  exact if_congr (by lia) rfl rfl

lemma rectColor_rowRect (k : ℕ) (x y : Fin 98) :
    rectColor (rowRect k) (x, y) = if y.val = 2 * k then 1 else 0 := by
  have hx := x.isLt
  unfold rectColor rowRect
  dsimp only
  exact if_congr (by lia) rfl rfl

lemma list_range_map_sum (n : ℕ) (f : ℕ → ZMod 2) :
    ((List.range n).map f).sum = ∑ k ∈ Finset.range n, f k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, Finset.sum_range_succ, ih]
    simp

lemma sum_ite_eq_double (x n : ℕ) (hx : x < 2 * n) :
    ∑ k ∈ Finset.range n, (if x = 2 * k then (1 : ZMod 2) else 0)
      = if Even x then 1 else 0 := by
  by_cases hev : Even x
  · obtain ⟨m, hm⟩ := hev
    rw [if_pos ⟨m, hm⟩, Finset.sum_eq_single m]
    · rw [if_pos (by lia)]
    · intro b _ hb
      rw [if_neg (by lia)]
    · intro hm'
      exact absurd (Finset.mem_range.mpr (by lia)) hm'
  · rw [if_neg hev, Finset.sum_eq_zero]
    intro k _
    rw [if_neg (fun h ↦ hev ⟨k, by lia⟩)]

lemma natCast_add_ite_even (m : ℕ) :
    ((m : ZMod 2) + if Even m then 1 else 0) = 1 := by
  by_cases h : Even m
  · rw [if_pos h, ZMod.natCast_eq_zero_iff_even.mpr h, zero_add]
  · rw [if_neg h, ZMod.natCast_eq_one_iff_odd.mpr (Nat.not_even_iff_odd.mp h), add_zero]

lemma construction_makes_zero (s : chessboard) :
    (((List.range 49).map colRect ++ (List.range 49).map rowRect).foldl
      recolor_rect start_coloring) s = 0 := by
  obtain ⟨x, y⟩ := s
  have hx := x.isLt
  have hy := y.isLt
  rw [foldl_recolor_apply, List.map_append, List.sum_append,
      List.map_map, List.map_map]
  have hcol : ((List.range 49).map (fun k ↦ rectColor (colRect k) (x, y))).sum
      = if Even x.val then 1 else 0 := by
    simp only [rectColor_colRect]
    rw [list_range_map_sum, sum_ite_eq_double x.val 49 (by lia)]
  have hrow : ((List.range 49).map (fun k ↦ rectColor (rowRect k) (x, y))).sum
      = if Even y.val then 1 else 0 := by
    simp only [rectColor_rowRect]
    rw [list_range_map_sum, sum_ite_eq_double y.val 49 (by lia)]
  simp only [Function.comp_def]
  rw [hcol, hrow]
  simp only [start_coloring]
  have h1 := natCast_add_ite_even x.val
  have h2 := natCast_add_ite_even y.val
  linear_combination h1 + h2 + CharTwo.add_self_eq_zero (1 : ZMod 2)

snip end

problem usa1998_p4 : IsLeast possible_num_clicks min_clicks := by
  constructor
  · exact ⟨(List.range 49).map colRect ++ (List.range 49).map rowRect,
      ⟨0, construction_makes_zero⟩, by simp⟩
  · rw [mem_lowerBounds]
    intro n hn
    obtain ⟨rs, ⟨c, hc⟩, hlen⟩ := hn
    have hdiff : (fun s ↦ (rs.map (fun r ↦ rectColor r s)).sum) = constAddStart c := by
      funext s
      have h1 := foldl_recolor_apply rs start_coloring s
      rw [hc s] at h1
      show _ = c + start_coloring s
      linear_combination - h1 - CharTwo.add_self_eq_zero (start_coloring s)
    have hupper := cornerSupport_listSum_card_le rs
    rw [hdiff] at hupper
    have hlower := target_support_card c
    rw [hlen] at hupper
    change 98 ≤ n
    lia

end Usa1998P4
