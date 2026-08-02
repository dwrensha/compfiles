/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Tactic
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.Analysis.InnerProductSpace.Convex
public import Mathlib.Analysis.Convex.StrictConvexBetween
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Olympiad 1968, Problem 4

Prove that in every tetrahedron there is a vertex such that the three edges
meeting there have lengths which are the sides of a triangle.
-/

namespace Imo1968P4

/-- Three real numbers that can be the side lengths of a (non-degenerate)
triangle: each of them is less than the sum of the other two. -/
def IsTriangle (x y z : ℝ) : Prop := x < y + z ∧ y < x + z ∧ z < x + y

snip begin

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {P : Type*} [MetricSpace P] [NormedAddTorsor V P]

/-- In an affinely independent family of four points (a tetrahedron), every
face is a genuine triangle: the strict triangle inequality holds. -/
theorem face_dist_lt {p : Fin 4 → P} (h : AffineIndependent ℝ p) {i j k : Fin 4}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    dist (p i) (p j) < dist (p i) (p k) + dist (p k) (p j) := by
  have hinj : Function.Injective ![i, k, j] := by
    intro x y hxy
    fin_cases x <;> fin_cases y <;> simp_all
  have h3 : AffineIndependent ℝ ![p i, p k, p j] := by
    have hcomp := h.comp_embedding (⟨![i, k, j], hinj⟩ : Fin 3 ↪ Fin 4)
    have heq : (p ∘ ⇑(⟨![i, k, j], hinj⟩ : Fin 3 ↪ Fin 4)) = ![p i, p k, p j] := by
      funext x
      fin_cases x <;> simp
    rwa [heq] at hcomp
  rw [affineIndependent_iff_not_collinear_set] at h3
  rw [dist_lt_dist_add_dist_iff]
  exact fun hw => h3 hw.collinear

/-- The triangle property is symmetric in the first two lengths. -/
theorem IsTriangle.swap₁₂ {x y z : ℝ} (h : IsTriangle x y z) : IsTriangle y x z := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨h2, h1, by linarith⟩

/-- The triangle property is symmetric in the last two lengths. -/
theorem IsTriangle.swap₂₃ {x y z : ℝ} (h : IsTriangle x y z) : IsTriangle x z y := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨by linarith, by linarith, by linarith⟩

/-- If the edge `AB` of a tetrahedron is at least as long as the other four
edges meeting `A` or `B`, then the three edges at `A` or the three edges at
`B` form a triangle. -/
theorem isTriangle_of_longest {A B C D : P}
    (hABC : dist A B < dist A C + dist C B)
    (hABD : dist A B < dist A D + dist D B)
    (hAC : dist A C ≤ dist A B) (hAD : dist A D ≤ dist A B)
    (hBC : dist B C ≤ dist A B) (hBD : dist B D ≤ dist A B) :
    IsTriangle (dist A B) (dist A C) (dist A D) ∨
    IsTriangle (dist A B) (dist B C) (dist B D) := by
  rw [dist_comm C B] at hABC
  rw [dist_comm D B] at hABD
  have hACpos : 0 < dist A C := by linarith
  have hADpos : 0 < dist A D := by linarith
  have hBCpos : 0 < dist B C := by linarith
  have hBDpos : 0 < dist B D := by linarith
  by_contra hcon
  push Not at hcon
  obtain ⟨hA, hB⟩ := hcon
  have hA' : dist A C + dist A D ≤ dist A B := by
    by_contra hlt
    push Not at hlt
    exact hA ⟨hlt, by linarith, by linarith⟩
  have hB' : dist B C + dist B D ≤ dist A B := by
    by_contra hlt
    push Not at hlt
    exact hB ⟨hlt, by linarith, by linarith⟩
  linarith

/-- Among six real numbers, one of them is at least as large as all the
others. -/
theorem exists_le_max6 (a b c d e f : ℝ) :
    (b ≤ a ∧ c ≤ a ∧ d ≤ a ∧ e ≤ a ∧ f ≤ a) ∨
    (a ≤ b ∧ c ≤ b ∧ d ≤ b ∧ e ≤ b ∧ f ≤ b) ∨
    (a ≤ c ∧ b ≤ c ∧ d ≤ c ∧ e ≤ c ∧ f ≤ c) ∨
    (a ≤ d ∧ b ≤ d ∧ c ≤ d ∧ e ≤ d ∧ f ≤ d) ∨
    (a ≤ e ∧ b ≤ e ∧ c ≤ e ∧ d ≤ e ∧ f ≤ e) ∨
    (a ≤ f ∧ b ≤ f ∧ c ≤ f ∧ d ≤ f ∧ e ≤ f) := by
  have ha : a ≤ max (max (max (max (max a b) c) d) e) f :=
    le_trans (le_max_left a b) (le_trans (le_max_left _ _)
      (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _))))
  have hb : b ≤ max (max (max (max (max a b) c) d) e) f :=
    le_trans (le_max_right a b) (le_trans (le_max_left _ _)
      (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _))))
  have hc : c ≤ max (max (max (max (max a b) c) d) e) f :=
    le_trans (le_max_right _ _) (le_trans (le_max_left _ _)
      (le_trans (le_max_left _ _) (le_max_left _ _)))
  have hd : d ≤ max (max (max (max (max a b) c) d) e) f :=
    le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_left _ _))
  have he : e ≤ max (max (max (max (max a b) c) d) e) f :=
    le_trans (le_max_right _ _) (le_max_left _ _)
  have hf : f ≤ max (max (max (max (max a b) c) d) e) f := le_max_right _ _
  rcases max_choice (max (max (max (max a b) c) d) e) f with h5 | h5
  · rcases max_choice (max (max (max a b) c) d) e with h4 | h4
    · rcases max_choice (max (max a b) c) d with h3 | h3
      · rcases max_choice (max a b) c with h2 | h2
        · rcases max_choice a b with h1 | h1
          · have hm := h5.trans (h4.trans (h3.trans (h2.trans h1)))
            exact Or.inl ⟨hb.trans (le_of_eq hm), hc.trans (le_of_eq hm),
              hd.trans (le_of_eq hm), he.trans (le_of_eq hm), hf.trans (le_of_eq hm)⟩
          · have hm := h5.trans (h4.trans (h3.trans (h2.trans h1)))
            exact Or.inr (Or.inl ⟨ha.trans (le_of_eq hm), hc.trans (le_of_eq hm),
              hd.trans (le_of_eq hm), he.trans (le_of_eq hm), hf.trans (le_of_eq hm)⟩)
        · have hm := h5.trans (h4.trans (h3.trans h2))
          exact Or.inr (Or.inr (Or.inl ⟨ha.trans (le_of_eq hm), hb.trans (le_of_eq hm),
            hd.trans (le_of_eq hm), he.trans (le_of_eq hm), hf.trans (le_of_eq hm)⟩))
      · have hm := h5.trans (h4.trans h3)
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨ha.trans (le_of_eq hm),
          hb.trans (le_of_eq hm), hc.trans (le_of_eq hm), he.trans (le_of_eq hm),
          hf.trans (le_of_eq hm)⟩)))
    · have hm := h5.trans h4
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ha.trans (le_of_eq hm),
        hb.trans (le_of_eq hm), hc.trans (le_of_eq hm), hd.trans (le_of_eq hm),
        hf.trans (le_of_eq hm)⟩))))
  · have hm := h5
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨ha.trans (le_of_eq hm),
      hb.trans (le_of_eq hm), hc.trans (le_of_eq hm), hd.trans (le_of_eq hm),
      he.trans (le_of_eq hm)⟩))))

snip end

problem imo1968_p4 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {P : Type*} [MetricSpace P] [NormedAddTorsor V P]
    (A B C D : P) (h : AffineIndependent ℝ ![A, B, C, D]) :
    IsTriangle (dist A B) (dist A C) (dist A D) ∨
    IsTriangle (dist B A) (dist B C) (dist B D) ∨
    IsTriangle (dist C A) (dist C B) (dist C D) ∨
    IsTriangle (dist D A) (dist D B) (dist D C) := by
  -- Each face of the tetrahedron is a genuine triangle.
  have hABCc : dist A B < dist A C + dist C B := by
    simpa using face_dist_lt (i := 0) (j := 1) (k := 2) h (by decide) (by decide) (by decide)
  have hABDd : dist A B < dist A D + dist D B := by
    simpa using face_dist_lt (i := 0) (j := 1) (k := 3) h (by decide) (by decide) (by decide)
  have hACb : dist A C < dist A B + dist B C := by
    simpa using face_dist_lt (i := 0) (j := 2) (k := 1) h (by decide) (by decide) (by decide)
  have hACd : dist A C < dist A D + dist D C := by
    simpa using face_dist_lt (i := 0) (j := 2) (k := 3) h (by decide) (by decide) (by decide)
  have hADb : dist A D < dist A B + dist B D := by
    simpa using face_dist_lt (i := 0) (j := 3) (k := 1) h (by decide) (by decide) (by decide)
  have hADc : dist A D < dist A C + dist C D := by
    simpa using face_dist_lt (i := 0) (j := 3) (k := 2) h (by decide) (by decide) (by decide)
  have hBCa : dist B C < dist B A + dist A C := by
    simpa using face_dist_lt (i := 1) (j := 2) (k := 0) h (by decide) (by decide) (by decide)
  have hBCd : dist B C < dist B D + dist D C := by
    simpa using face_dist_lt (i := 1) (j := 2) (k := 3) h (by decide) (by decide) (by decide)
  have hBDa : dist B D < dist B A + dist A D := by
    simpa using face_dist_lt (i := 1) (j := 3) (k := 0) h (by decide) (by decide) (by decide)
  have hBDc : dist B D < dist B C + dist C D := by
    simpa using face_dist_lt (i := 1) (j := 3) (k := 2) h (by decide) (by decide) (by decide)
  have hCDa : dist C D < dist C A + dist A D := by
    simpa using face_dist_lt (i := 2) (j := 3) (k := 0) h (by decide) (by decide) (by decide)
  have hCDb : dist C D < dist C B + dist B D := by
    simpa using face_dist_lt (i := 2) (j := 3) (k := 1) h (by decide) (by decide) (by decide)
  -- Case split on which of the six edges is a longest one.
  rcases exists_le_max6 (dist A B) (dist A C) (dist A D) (dist B C) (dist B D) (dist C D) with
    ⟨h1, h2, h3, h4, h5⟩ | ⟨h1, h2, h3, h4, h5⟩ | ⟨h1, h2, h3, h4, h5⟩ |
    ⟨h1, h2, h3, h4, h5⟩ | ⟨h1, h2, h3, h4, h5⟩ | ⟨h1, h2, h3, h4, h5⟩
  · -- `AB` is a longest edge: one of `A`, `B` works.
    rcases isTriangle_of_longest hABCc hABDd h1 h2 h3 h4 with ht | ht
    · exact Or.inl ht
    · exact Or.inr (Or.inl (by rwa [dist_comm B A]))
  · -- `AC` is a longest edge: one of `A`, `C` works.
    rcases isTriangle_of_longest hACb hACd h1 h2 (by rwa [dist_comm C B]) h5 with ht | ht
    · exact Or.inl ht.swap₁₂
    · exact Or.inr (Or.inr (Or.inl (by rwa [dist_comm C A])))
  · -- `AD` is a longest edge: one of `A`, `D` works.
    rcases isTriangle_of_longest hADb hADc h1 h2 (by rwa [dist_comm D B])
      (by rwa [dist_comm D C]) with ht | ht
    · exact Or.inl ht.swap₁₂.swap₂₃
    · exact Or.inr (Or.inr (Or.inr (by rwa [dist_comm D A])))
  · -- `BC` is a longest edge: one of `B`, `C` works.
    rcases isTriangle_of_longest hBCa hBCd (by rwa [dist_comm B A]) h4
      (by rwa [dist_comm C A]) h5 with ht | ht
    · exact Or.inr (Or.inl ht.swap₁₂)
    · exact Or.inr (Or.inr (Or.inl (by rw [dist_comm C B]; exact ht.swap₁₂)))
  · -- `BD` is a longest edge: one of `B`, `D` works.
    rcases isTriangle_of_longest hBDa hBDc (by rwa [dist_comm B A]) h4
      (by rwa [dist_comm D A]) (by rwa [dist_comm D C]) with ht | ht
    · exact Or.inr (Or.inl ht.swap₁₂.swap₂₃)
    · exact Or.inr (Or.inr (Or.inr (by rw [dist_comm D B]; exact ht.swap₁₂)))
  · -- `CD` is a longest edge: one of `C`, `D` works.
    rcases isTriangle_of_longest hCDa hCDb (by rwa [dist_comm C A]) (by rwa [dist_comm C B])
      (by rwa [dist_comm D A]) (by rwa [dist_comm D B]) with ht | ht
    · exact Or.inr (Or.inr (Or.inl ht.swap₁₂.swap₂₃))
    · exact Or.inr (Or.inr (Or.inr (by rw [dist_comm D C]; exact ht.swap₁₂.swap₂₃)))

end Imo1968P4
