/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Data.Real.Basic
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Algebra] }

/-!
# USA Mathematical Olympiad 1987, Problem 3

X is the smallest set of polynomials p(x) such that:
(1) p(x) = x belongs to X; and
(2) if r(x) belongs to X, then x·r(x) and (x + (1 - x)·r(x)) both belong to X.

Show that if r(x) and s(x) are distinct elements of X, then r(x) ≠ s(x)
for any 0 < x < 1.
-/

namespace Usa1987P3

open Polynomial

snip begin

/-- The set `X` of the problem, as an inductive predicate: it is the smallest
set of polynomials that contains the identity polynomial `X` and is closed
under the two operations `r ↦ X * r` and `r ↦ X + (1 - X) * r`. -/
inductive InX : Polynomial ℝ → Prop
  | base : InX X
  | mul {r : Polynomial ℝ} (hr : InX r) : InX (X * r)
  | comb {r : Polynomial ℝ} (hr : InX r) : InX (X + (1 - X) * r)

/-- Every polynomial of `X` maps the open interval `(0, 1)` into itself. -/
lemma InX.eval_mem_Ioo {r : Polynomial ℝ} (hr : InX r)
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    0 < r.eval x ∧ r.eval x < 1 := by
  induction hr with
  | base =>
      rw [eval_X]
      exact ⟨hx0, hx1⟩
  | mul _ ih =>
      simp only [eval_mul, eval_X]
      exact ⟨mul_pos hx0 ih.1,
        ((mul_lt_mul_of_pos_left ih.2 hx0).trans_eq (mul_one x)).trans hx1⟩
  | comb _ ih =>
      simp only [eval_add, eval_mul, eval_sub, eval_X, eval_one]
      have h2 := add_lt_add_right (mul_lt_mul_of_pos_left ih.2 (sub_pos.mpr hx1)) x
      rw [mul_one, add_sub_cancel] at h2
      exact ⟨add_pos hx0 (mul_pos (sub_pos.mpr hx1) ih.1), h2⟩

/-- The key trichotomy: two elements of `X` are either equal as polynomials,
or one of them is strictly smaller than the other throughout the whole open
interval `(0, 1)`. The proof goes by induction on the construction of `r`
and case analysis on the construction of `s`; it is a form of lexicographic
comparison of the operation sequences (cf. the informal solution, where
`+` counts as larger than "no further operation", which in turn counts as
larger than `-`). -/
lemma InX.trichotomy {r : Polynomial ℝ} (hr : InX r) :
    ∀ {s : Polynomial ℝ}, InX s →
      r = s ∨ (∀ x : ℝ, 0 < x → x < 1 → r.eval x < s.eval x) ∨
              (∀ x : ℝ, 0 < x → x < 1 → s.eval x < r.eval x) := by
  induction hr with
  | base =>
      intro s hs
      cases hs with
      | base => exact Or.inl rfl
      | mul h =>
          refine Or.inr (Or.inr fun x hx0 hx1 ↦ ?_)
          simp only [eval_mul, eval_X]
          exact (mul_lt_mul_of_pos_left (h.eval_mem_Ioo hx0 hx1).2 hx0).trans_eq (mul_one x)
      | comb h =>
          refine Or.inr (Or.inl fun x hx0 hx1 ↦ ?_)
          simp only [eval_add, eval_mul, eval_sub, eval_X, eval_one]
          exact lt_add_of_pos_right x (mul_pos (sub_pos.mpr hx1) (h.eval_mem_Ioo hx0 hx1).1)
  | mul h ihr =>
      intro s hs
      cases hs with
      | base =>
          refine Or.inr (Or.inl fun x hx0 hx1 ↦ ?_)
          simp only [eval_mul, eval_X]
          exact (mul_lt_mul_of_pos_left (h.eval_mem_Ioo hx0 hx1).2 hx0).trans_eq (mul_one x)
      | mul h' =>
          rcases ihr h' with he | hlt | hgt
          · exact Or.inl (by rw [he])
          · refine Or.inr (Or.inl fun x hx0 hx1 ↦ ?_)
            simp only [eval_mul, eval_X]
            exact mul_lt_mul_of_pos_left (hlt x hx0 hx1) hx0
          · refine Or.inr (Or.inr fun x hx0 hx1 ↦ ?_)
            simp only [eval_mul, eval_X]
            exact mul_lt_mul_of_pos_left (hgt x hx0 hx1) hx0
      | comb h' =>
          refine Or.inr (Or.inl fun x hx0 hx1 ↦ ?_)
          simp only [eval_add, eval_mul, eval_sub, eval_X, eval_one]
          have hr' := h.eval_mem_Ioo hx0 hx1
          have hs' := h'.eval_mem_Ioo hx0 hx1
          exact ((mul_lt_mul_of_pos_left hr'.2 hx0).trans_eq (mul_one x)).trans
            (lt_add_of_pos_right x (mul_pos (sub_pos.mpr hx1) hs'.1))
  | comb h ihr =>
      intro s hs
      cases hs with
      | base =>
          refine Or.inr (Or.inr fun x hx0 hx1 ↦ ?_)
          simp only [eval_add, eval_mul, eval_sub, eval_X, eval_one]
          exact lt_add_of_pos_right x (mul_pos (sub_pos.mpr hx1) (h.eval_mem_Ioo hx0 hx1).1)
      | mul h' =>
          refine Or.inr (Or.inr fun x hx0 hx1 ↦ ?_)
          simp only [eval_add, eval_mul, eval_sub, eval_X, eval_one]
          have hr' := h.eval_mem_Ioo hx0 hx1
          have hs' := h'.eval_mem_Ioo hx0 hx1
          exact ((mul_lt_mul_of_pos_left hs'.2 hx0).trans_eq (mul_one x)).trans
            (lt_add_of_pos_right x (mul_pos (sub_pos.mpr hx1) hr'.1))
      | comb h' =>
          rcases ihr h' with he | hlt | hgt
          · exact Or.inl (by rw [he])
          · refine Or.inr (Or.inl fun x hx0 hx1 ↦ ?_)
            simp only [eval_add, eval_mul, eval_sub, eval_X, eval_one]
            exact add_lt_add_right
              (mul_lt_mul_of_pos_left (hlt x hx0 hx1) (sub_pos.mpr hx1)) x
          · refine Or.inr (Or.inr fun x hx0 hx1 ↦ ?_)
            simp only [eval_add, eval_mul, eval_sub, eval_X, eval_one]
            exact add_lt_add_right
              (mul_lt_mul_of_pos_left (hgt x hx0 hx1) (sub_pos.mpr hx1)) x

snip end

problem usa1987_p3
    (S : Set (Polynomial ℝ))
    (_hX : Polynomial.X ∈ S)
    (_hmul : ∀ r ∈ S, Polynomial.X * r ∈ S)
    (_hcomb : ∀ r ∈ S, Polynomial.X + (1 - Polynomial.X) * r ∈ S)
    (hmin : ∀ T : Set (Polynomial ℝ), Polynomial.X ∈ T →
        (∀ r ∈ T, Polynomial.X * r ∈ T) →
        (∀ r ∈ T, Polynomial.X + (1 - Polynomial.X) * r ∈ T) → S ⊆ T)
    {r s : Polynomial ℝ} (hr : r ∈ S) (hs : s ∈ S) (hne : r ≠ s)
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    r.eval x ≠ s.eval x := by
  have hsub : S ⊆ {p : Polynomial ℝ | InX p} :=
    hmin _ InX.base (fun _ h ↦ InX.mul h) (fun _ h ↦ InX.comb h)
  rcases InX.trichotomy (hsub hr) (hsub hs) with he | hlt | hgt
  · exact absurd he hne
  · exact ne_of_lt (hlt x hx0 hx1)
  · exact ne_of_gt (hgt x hx0 hx1)

end Usa1987P3
