/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: sjfhsjfh
-/
import Mathlib

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# China Pre-CMO (National High School Math League, Second Round) 1986, Problem 3

平面直角坐标系中, 纵、横坐标都是整数的点称为整点 (lattice point).
请设计一种方法将所有的整点染色, 每一个整点染成白色、红色或黑色中的一种颜色, 使得
(1) 三种颜色的点出现在无穷多条平行于横轴的直线上无穷多次;
(2) 对任意白点 `A`、红点 `B` 和黑点 `C`, 总可以找到一个红点 `D`, 使得 `ABCD` 为一平行四边形.
证明你设计的方法符合上述要求.

Design a coloring of all lattice points `ℤ × ℤ` with three colors — white, red, black — such that
(1) on infinitely many horizontal lines, each color appears infinitely many times;
(2) for any white point `A`, red point `B`, and black point `C`, there exists a red point `D`
such that `ABCD` is a parallelogram.
Prove that your coloring satisfies the requirements.
-/

namespace ChinaPre1986P3

inductive Color where
| white
| red
| black
deriving DecidableEq, Fintype

determine f : ℤ × ℤ → Color
  | (x, _) =>
    let r := x % 3
    if r = 0 then .white
    else if r = 1 then .red
    else .black

snip begin

lemma f_eq_white_iff (x y : ℤ) : f (x, y) = .white ↔ x % 3 = 0 := by
  simp only [f]; split_ifs <;> tauto

lemma f_eq_red_iff (x y : ℤ) : f (x, y) = .red ↔ x % 3 = 1 := by
  simp only [f]; split_ifs with h h'
  <;> simp only [h, zero_ne_one, true_iff, false_iff]
  <;> simp only [h', not_false_eq_true]

lemma f_eq_black_iff (x y : ℤ) : f (x, y) = .black ↔ x % 3 = 2 := by
  simp only [f]; split_ifs with h h'
  <;> simp only [h, true_iff, false_iff, OfNat.zero_ne_ofNat]
  <;> omega

snip end

problem chinaPre1986_p3
  : (∀ (c : Color),
      Set.Infinite {y : ℤ | Set.Infinite {x : ℤ | f (x, y) = c}})
  ∧ (∀ (A B C : ℤ × ℤ),
      f A = .white → f B = .red → f C = .black → ∃ (D : ℤ × ℤ),
      f D = .red ∧ A.1 + C.1 = B.1 + D.1 ∧ A.2 + C.2 = B.2 + D.2) := by
  refine ⟨fun c ↦ ?_, fun A B C hA hB hC ↦ ?_⟩
  · have h_inner (y : ℤ) : Set.Infinite {x : ℤ | f (x, y) = c} := by
      rcases c with (white | red | black)
      <;> simp only [f_eq_white_iff _ y, f_eq_red_iff _ y, f_eq_black_iff _ y]
      · refine (Set.infinite_range_of_injective (f := fun z : ℤ ↦ 3 * z) ?_).mono ?_
        · intro z₁ z₂; simp only; norm_num
        · rintro z ⟨n, rfl⟩; norm_num
      · refine (Set.infinite_range_of_injective (f := fun z : ℤ ↦ 3 * z + 1) ?_).mono ?_
        · intro z₁ z₂; simp only; norm_num
        · rintro z ⟨n, rfl⟩; norm_num
      · refine (Set.infinite_range_of_injective (f := fun z : ℤ ↦ 3 * z + 2) ?_).mono ?_
        · intro z₁ z₂; simp only; norm_num
        · rintro z ⟨n, rfl⟩; norm_num
    have h_outer : {y : ℤ | Set.Infinite {x : ℤ | f (x, y) = c}} = Set.univ := by
      ext y; simp only [h_inner y, Set.setOf_true, Set.mem_univ]
    rewrite [h_outer]; exact Set.infinite_univ
  · use ⟨A.1 + C.1 - B.1, A.2 + C.2 - B.2⟩
    simp only [add_sub_cancel, and_self, and_true]
    have hA_mod : A.1 % 3 = 0 := ((f_eq_white_iff A.1 A.2).mp hA)
    have hB_mod : B.1 % 3 = 1 := ((f_eq_red_iff B.1 B.2).mp hB)
    have hC_mod : C.1 % 3 = 2 := ((f_eq_black_iff C.1 C.2).mp hC)
    have hD_mod : (A.1 + C.1 - B.1) % 3 = 1 := by omega
    exact (f_eq_red_iff (A.1 + C.1 - B.1) (A.2 + C.2 - B.2)).mpr hD_mod

end ChinaPre1986P3
