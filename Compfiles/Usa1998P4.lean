/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.Order.Bounds.Basic

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

problem usa1998_p4 : IsLeast possible_num_clicks min_clicks := by
  constructor
  · use (List.range 49).map
      (λ x ↦ ⟨2 * x, 0, 1, 98⟩) ++ (List.range 49).map (λ y ↦ ⟨0, 2 * y, 98, 1⟩)
    constructor
    · use 0
      intro s
      sorry
    · simp only [List.length_append, List.length_map, List.length_range]
  · rw[mem_lowerBounds]
    intro n hn
    obtain ⟨rs, hrs, hrsl⟩ := hn
    sorry



end Usa1998P4
