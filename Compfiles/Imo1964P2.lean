/-
Copyright (c) 2024 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra, .Inequality] }

/-!
# International Mathematical Olympiad 1964, Problem 2

Suppose that a,b,c are the side lengths of a triangle. Prove that

   a²(b + c - a) + b²(c + a - b) + c²(a + b - c) ≤ 3abc.
-/

namespace Imo1964P2

snip begin

-- TODO: get this into mathlib in some form
lemma schur {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    0 ≤ a * (a - b) * (a - c) + b * (b - a) * (b - c) + c * (c - a) * (c - b) := by
  -- from https://artofproblemsolving.com/wiki/index.php/Schur%27s_Inequality
  wlog Hcb : c ≤ b with h1
  · have h3 : b ≤ c := le_of_not_le Hcb
    linarith [h1 ha hc hb h3]
  wlog Hba : b ≤ a with h2
  · have h4 : a ≤ b := le_of_not_le Hba
    obtain hca | hac : c ≤ a ∨ a ≤ c := le_total c a
    · have := h2 hb ha hc hca h4
      linarith only [this]
    · have := h2 hb hc ha hac Hcb
      linarith only [this]
  have h5 :=
    calc a * (a - b) * (a - c) + b * (b - a) * (b - c)
       = a * (a - b) * (a - c) - b * (a - b) * (b - c) := by ring
     _ = (a - b) * (a * (a - c)- b * (b - c)) := by ring

  have h6 : 0 ≤ (a - b) * (a * (a - c) - b * (b - c)) := by
    have h7 : 0 ≤ a - b := sub_nonneg.mpr Hba
    have h8 : 0 ≤ b - c := sub_nonneg.mpr Hcb
    have h10 : b - c ≤ a - c := sub_le_sub_right Hba c
    suffices h11 : 0 ≤ (a * (a-c)-b * (b-c)) from
      mul_nonneg h7 h11
    have h12 : a * (b - c) ≤ a * (a - c) := mul_le_mul_of_nonneg_left h10 ha
    have h13 : 0 ≤ a * (b - c) - b * (b - c) := by
      rw [←sub_mul]; positivity
    have h14 : a * (b - c) - b * (b - c) ≤  a * (a - c) - b * (b - c) :=
      sub_le_sub_right h12 (b * (b - c))
    exact le_trans h13 h14

  rw [← h5] at h6
  have h12 : 0 ≤ (c - a) * (c - b) := by nlinarith only [Hba, Hcb]
  have h13 : 0 ≤ c * (c - a) * (c - b) := by nlinarith only [hc, h12]
  linarith

snip end

problem imo1964_p2
    (T : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2)))
    (a b c : ℝ)
    (ha : a = dist (T.points 1) (T.points 2))
    (hb : b = dist (T.points 2) (T.points 0))
    (hc : c = dist (T.points 0) (T.points 1)) :
    a^2 * (b + c - a) + b^2 * (c + a - b) + c^2 * (a + b - c) ≤
    3 * a * b * c := by
  -- solution 3 from
  -- https://artofproblemsolving.com/wiki/index.php/1964_IMO_Problems/Problem_2

  -- The only thing we need to know about a,b,c is that they
  -- are nonnegative.
  have ha' : 0 ≤ dist (T.points 1) (T.points 2) := dist_nonneg
  rw [←ha] at ha'; clear ha
  have hb' : 0 ≤ dist (T.points 2) (T.points 0) := dist_nonneg
  rw [←hb] at hb'; clear hb
  have hc' : 0 ≤ dist (T.points 0) (T.points 1) := dist_nonneg
  rw [←hc] at hc'; clear hc
  clear T

  have h1 :
      3 * a * b * c - (a^2 * (b + c - a) + b^2 * (c + a - b) + c^2 * (a + b - c)) =
      a * (a - b) * (a - c) + b * (b - a) * (b - c) + c * (c - a) * (c - b) := by
    ring
  suffices 0 ≤
    3 * a * b * c - (a^2 * (b + c - a) + b^2 * (c + a - b) + c^2 * (a + b - c)) from
    sub_nonneg.mp this
  rw [h1]
  exact schur ha' hb' hc'
