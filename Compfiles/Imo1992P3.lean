/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Tactic
public import Mathlib.Data.Finset.Sym
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Olympiad 1992, Problem 3

Consider 9 points in space, no 4 coplanar. Each pair of points is joined by a
line segment which is colored either blue or red or left uncolored. Find the
smallest value of n such that whenever exactly n edges are colored, the set of
colored edges necessarily contains a triangle all of whose edges have the same
color.
-/

namespace Imo1992P3

/-- An edge coloring of the complete graph on 9 vertices by two colors
(encoded as `Fin 2`), where some edges may be left uncolored (`none`).
The vertices are indexed by `Fin 9` and the edges by unordered pairs
`Sym2 (Fin 9)`; the geometric hypotheses of the problem (9 points in space,
no 4 of them coplanar) only serve to guarantee that every pair of points
determines an edge, so the problem is purely combinatorial. -/
structure EdgeColoring where
  /-- the color assigned to the edge joining two vertices -/
  color : Sym2 (Fin 9) → Option (Fin 2)
  /-- there is no edge from a vertex to itself -/
  diag : ∀ i : Fin 9, color s(i, i) = none

/-- The colored edges of an edge coloring, represented as the set of edges
that received a color. (Diagonal "edges" `s(i, i)` are never colored, so this
is exactly the set of colored segments joining two distinct points.) -/
def EdgeColoring.coloredEdges (c : EdgeColoring) : Finset (Sym2 (Fin 9)) :=
  Finset.filter (fun e => (c.color e).isSome) Finset.univ

/-- The uncolored edges of an edge coloring, represented as the set of
non-diagonal edges that were left uncolored. -/
def EdgeColoring.uncoloredEdges (c : EdgeColoring) : Finset (Sym2 (Fin 9)) :=
  Finset.filter (fun e => c.color e = none ∧ ¬ e.IsDiag) Finset.univ

/-- A coloring has a monochromatic triangle if there are three distinct
vertices whose three connecting edges all have the same color. -/
def EdgeColoring.HasMonoTriangle (c : EdgeColoring) : Prop :=
  ∃ i j k : Fin 9, i ≠ j ∧ j ≠ k ∧ k ≠ i ∧
    ∃ b : Fin 2, c.color s(i, j) = some b ∧ c.color s(j, k) = some b ∧
      c.color s(k, i) = some b

snip begin

/-- In `Fin 2`, two elements different from a common one are equal. -/
lemma fin2_eq_of_ne (u v b : Fin 2) (hu : u ≠ b) (hv : v ≠ b) : u = v := by
  revert u v b
  decide

/-- The Ramsey fact `R(3,3) ≤ 6`: every red/blue coloring of the edges of the
complete graph on 6 vertices contains a monochromatic triangle. -/
lemma ramsey6 (f : Fin 6 → Fin 6 → Fin 2) (hsym : ∀ i j, f i j = f j i) :
    ∃ i j k : Fin 6, i ≠ j ∧ j ≠ k ∧ k ≠ i ∧ f i j = f j k ∧ f j k = f k i := by
  -- Among the 5 edges leaving vertex `0`, at least 3 have the same color `b`.
  have hcard : ((Finset.univ : Finset (Fin 6)).erase 0).card = 5 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Fintype.card_fin]
  have hsum : ((Finset.univ : Finset (Fin 6)).erase 0).card = ∑ b : Fin 2,
      (((Finset.univ : Finset (Fin 6)).erase 0).filter
        fun j => f 0 j = b).card :=
    Finset.card_eq_sum_card_fiberwise (fun j _ => Finset.mem_univ (f 0 j))
  rw [hcard] at hsum
  obtain ⟨b, hb⟩ : ∃ b : Fin 2, 3 ≤ (((Finset.univ : Finset (Fin 6)).erase 0).filter
      fun j => f 0 j = b).card := by
    by_contra h
    push Not at h
    have hle : ∑ b : Fin 2, (((Finset.univ : Finset (Fin 6)).erase 0).filter
        fun j => f 0 j = b).card ≤ ∑ _b : Fin 2, 2 :=
      Finset.sum_le_sum fun b _ => Nat.le_of_lt_succ (h b)
    have hfour : ∑ _b : Fin 2, (2 : ℕ) = 4 := by norm_num [Fin.sum_univ_two]
    lia
  -- Pick three distinct vertices `x y z` joined to `0` by an edge of color `b`.
  have hFpos : 0 < (((Finset.univ : Finset (Fin 6)).erase 0).filter
      fun j => f 0 j = b).card := by lia
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hFpos
  have hF2 : 1 < ((((Finset.univ : Finset (Fin 6)).erase 0).filter
      fun j => f 0 j = b).erase x).card := by
    rw [Finset.card_erase_of_mem hx]; lia
  obtain ⟨y, hy, z, hz, hyz⟩ := Finset.one_lt_card.mp hF2
  have hyF : y ∈ ((Finset.univ : Finset (Fin 6)).erase 0).filter
      (fun j => f 0 j = b) := Finset.mem_of_mem_erase hy
  have hzF : z ∈ ((Finset.univ : Finset (Fin 6)).erase 0).filter
      (fun j => f 0 j = b) := Finset.mem_of_mem_erase hz
  have hxy : x ≠ y := fun h => Finset.ne_of_mem_erase hy h.symm
  have hzx : z ≠ x := Finset.ne_of_mem_erase hz
  have hmem : ∀ {w : Fin 6}, w ∈ ((Finset.univ : Finset (Fin 6)).erase 0).filter
      (fun j => f 0 j = b) → w ≠ 0 ∧ f 0 w = b := by
    intro w hw
    rw [Finset.mem_filter, Finset.mem_erase] at hw
    exact ⟨hw.1.1, hw.2⟩
  obtain ⟨hx0, hfx⟩ := hmem hx
  obtain ⟨hy0, hfy⟩ := hmem hyF
  obtain ⟨hz0, hfz⟩ := hmem hzF
  have fyx : f y 0 = b := (hsym y 0).trans hfy
  have fzx : f z 0 = b := (hsym z 0).trans hfz
  -- If one of the edges `xy`, `yz`, `xz` has color `b` we get a triangle
  -- through `0`; otherwise `xyz` itself is monochromatic.
  by_cases hxy' : f x y = b
  · exact ⟨0, x, y, hx0.symm, hxy, hy0, hfx.trans hxy'.symm, hxy'.trans fyx.symm⟩
  · by_cases hyz' : f y z = b
    · exact ⟨0, y, z, hy0.symm, hyz, hz0, hfy.trans hyz'.symm, hyz'.trans fzx.symm⟩
    · by_cases hxz' : f x z = b
      · exact ⟨0, x, z, hx0.symm, hzx.symm, hz0, hfx.trans hxz'.symm,
          hxz'.trans fzx.symm⟩
      · exact ⟨x, y, z, hxy, hyz, hzx, fin2_eq_of_ne _ _ _ hxy' hyz',
          (fin2_eq_of_ne _ _ _ hyz' hxz').trans (hsym z x).symm⟩

/-- The smaller endpoint of an edge, well-defined since `min` is symmetric. -/
def minEndpoint (e : Sym2 (Fin 9)) : Fin 9 :=
  Sym2.lift ⟨fun i j => min i j, fun _ _ => min_comm _ _⟩ e

lemma minEndpoint_mk (i j : Fin 9) : minEndpoint s(i, j) = min i j := rfl

/-- First part: any coloring with at least 33 colored edges contains a
monochromatic triangle. -/
lemma mono_triangle_of_colored_ge (c : EdgeColoring)
    (h : 33 ≤ c.coloredEdges.card) : c.HasMonoTriangle := by
  -- There are at most 3 uncolored edges.
  have hpairs : ((Finset.univ : Finset (Sym2 (Fin 9))).filter
      fun e => ¬ e.IsDiag).card = 36 := by decide
  -- A diagonal "edge" is never colored.
  have hoff : ∀ e : Sym2 (Fin 9), (c.color e).isSome → ¬ e.IsDiag := by
    intro e he hdiag
    induction e using Sym2.ind with
    | _ i j =>
      rw [Sym2.mk_isDiag_iff] at hdiag
      subst hdiag
      simp [c.diag] at he
  have hcong_col : c.coloredEdges = ((Finset.univ : Finset (Sym2 (Fin 9))).filter
      fun e => ¬ e.IsDiag).filter fun e => (c.color e).isSome := by
    simp only [EdgeColoring.coloredEdges, Finset.filter_filter]
    apply Finset.filter_congr
    intro e _
    exact ⟨fun he => ⟨hoff e he, he⟩, And.right⟩
  have hcong_uncol : c.uncoloredEdges = ((Finset.univ : Finset (Sym2 (Fin 9))).filter
      fun e => ¬ e.IsDiag).filter fun e => ¬ (c.color e).isSome := by
    simp only [EdgeColoring.uncoloredEdges, Finset.filter_filter]
    apply Finset.filter_congr
    intro e _
    rw [Option.not_isSome_iff_eq_none, and_comm]
  have hsum : c.coloredEdges.card + c.uncoloredEdges.card = 36 := by
    rw [← hpairs, hcong_col, hcong_uncol]
    exact Finset.card_filter_add_card_filter_not _
  have huncol : c.uncoloredEdges.card ≤ 3 := by lia
  -- The smaller endpoints of the uncolored edges form a set `C` of at most
  -- 3 vertices covering every uncolored edge.
  set C := c.uncoloredEdges.image minEndpoint with hCdef
  have hC : C.card ≤ 3 := le_trans Finset.card_image_le huncol
  have cover : ∀ i j : Fin 9, i ≠ j → c.color s(i, j) = none → min i j ∈ C := by
    intro i j hij hc
    have hmem : s(i, j) ∈ c.uncoloredEdges :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc,
        fun hd => hij (Sym2.mk_isDiag_iff.1 hd)⟩
    rw [hCdef, ← minEndpoint_mk i j]
    exact Finset.mem_image_of_mem minEndpoint hmem
  -- So any two distinct vertices outside `C` are joined by a colored edge.
  have hcol : ∀ i ∈ (Finset.univ : Finset (Fin 9)) \ C,
      ∀ j ∈ (Finset.univ : Finset (Fin 9)) \ C, i ≠ j → (c.color s(i, j)).isSome := by
    intro i hi j hj hij
    cases hc : c.color s(i, j) with
    | none =>
      have hmin := cover i j hij hc
      rcases min_choice i j with hmin' | hmin'
      · rw [hmin'] at hmin
        exact absurd hmin (Finset.mem_sdiff.mp hi).2
      · rw [hmin'] at hmin
        exact absurd hmin (Finset.mem_sdiff.mp hj).2
    | some b => simp
  -- There are at least 6 vertices outside `C`; pick 6 of them.
  have hs : 6 ≤ ((Finset.univ : Finset (Fin 9)) \ C).card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ C), Finset.card_univ,
      Fintype.card_fin]
    lia
  obtain ⟨t, hts, ht⟩ := Finset.exists_subset_card_eq hs
  -- Reindex these 6 vertices by `Fin 6` and apply the Ramsey fact.
  let e := t.orderIsoOfFin ht
  let g : Fin 6 → Fin 9 := fun a => (e a : Fin 9)
  have hg : Function.Injective g := fun a b hab => e.injective (Subtype.ext hab)
  have hgs : ∀ a : Fin 6, g a ∈ (Finset.univ : Finset (Fin 9)) \ C :=
    fun a => hts (e a).2
  let f : Fin 6 → Fin 6 → Fin 2 := fun a b => (c.color s(g a, g b)).getD 0
  have fsym : ∀ a b : Fin 6, f a b = f b a := by
    intro a b
    show (c.color s(g a, g b)).getD 0 = (c.color s(g b, g a)).getD 0
    rw [Sym2.eq_swap]
  have key : ∀ a b : Fin 6, a ≠ b → c.color s(g a, g b) = some (f a b) := by
    intro a b hab
    have hsome := hcol (g a) (hgs a) (g b) (hgs b) (fun h => hab (hg h))
    cases hv : c.color s(g a, g b) with
    | none => simp [hv] at hsome
    | some v =>
      have hfv : f a b = v := by
        show (c.color s(g a, g b)).getD 0 = v
        rw [hv, Option.getD_some]
      rw [hfv]
  obtain ⟨a, b, k, hab, hbk, hka, h1, h2⟩ := ramsey6 f fsym
  refine ⟨g a, g b, g k, fun h => hab (hg h), fun h => hbk (hg h),
    fun h => hka (hg h), f a b, key a b hab, ?_, ?_⟩
  · rw [h1]; exact key b k hbk
  · rw [h1, h2]; exact key k a hka

/-- The extremal coloring on 32 edges (Wöginger's construction):
vertices `0,…,3` form the red square, `4,…,7` the blue square, and `8` is the
apex. The diagonals of the two squares are the four uncolored edges. -/
def auxColor : Sym2 (Fin 9) → Option (Fin 2) :=
  Sym2.lift ⟨fun i j =>
    if i = j then none
    else if i.val ≤ 3 ∧ j.val ≤ 3 then
      if i.val % 2 = j.val % 2 then none else some 0
    else if 4 ≤ i.val ∧ i.val ≤ 7 ∧ 4 ≤ j.val ∧ j.val ≤ 7 then
      if i.val % 2 = j.val % 2 then none else some 1
    else if (i.val ≤ 3 ∧ 4 ≤ j.val ∧ j.val ≤ 7) ∨
        (j.val ≤ 3 ∧ 4 ≤ i.val ∧ i.val ≤ 7) then
      if i.val % 2 = j.val % 2 then some 0 else some 1
    else if i.val ≤ 3 ∨ j.val ≤ 3 then some 1
    else some 0, by decide⟩

lemma auxColor_diag : ∀ i : Fin 9, auxColor s(i, i) = none := by
  decide

/-- The extremal coloring, packaged as an `EdgeColoring`. -/
def auxColoring : EdgeColoring where
  color := auxColor
  diag := auxColor_diag

lemma aux_colored_card : auxColoring.coloredEdges.card = 32 := by
  decide

lemma aux_no_mono : ¬ auxColoring.HasMonoTriangle := by
  unfold EdgeColoring.HasMonoTriangle
  decide

/-- Uncoloring the edges of `P` in the extremal coloring. -/
def shrinkColor (P : Finset (Sym2 (Fin 9))) : Sym2 (Fin 9) → Option (Fin 2) :=
  fun e => if e ∈ P then none else auxColor e

lemma shrinkColor_apply (P : Finset (Sym2 (Fin 9))) (e : Sym2 (Fin 9)) :
    shrinkColor P e = if e ∈ P then none else auxColor e := rfl

lemma shrinkColor_diag (P : Finset (Sym2 (Fin 9))) :
    ∀ i : Fin 9, shrinkColor P s(i, i) = none := by
  intro i
  rw [shrinkColor_apply]
  by_cases h : s(i, i) ∈ P
  · rw [ite_eq_left h]
  · rw [ite_eq_right h]
    exact auxColor_diag i

/-- The shrunk coloring, packaged as an `EdgeColoring`. -/
def shrinkColoring (P : Finset (Sym2 (Fin 9))) : EdgeColoring where
  color := shrinkColor P
  diag := shrinkColor_diag P

lemma shrinkColor_some_of {P : Finset (Sym2 (Fin 9))} {e : Sym2 (Fin 9)} {b : Fin 2}
    (h : shrinkColor P e = some b) : auxColor e = some b := by
  rw [shrinkColor_apply] at h
  by_cases hc : e ∈ P
  · rw [ite_eq_left hc] at h
    simp at h
  · rw [ite_eq_right hc] at h
    exact h

lemma shrink_coloredEdges (P : Finset (Sym2 (Fin 9))) :
    (shrinkColoring P).coloredEdges = auxColoring.coloredEdges \ P := by
  have hcolor : ∀ e : Sym2 (Fin 9), (shrinkColoring P).color e = shrinkColor P e :=
    fun _ => rfl
  ext e
  simp only [EdgeColoring.coloredEdges, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_sdiff]
  rw [hcolor e]
  constructor
  · intro hsome
    by_cases hc : e ∈ P
    · rw [shrinkColor_apply, ite_eq_left hc] at hsome
      simp at hsome
    · rw [shrinkColor_apply, ite_eq_right hc] at hsome
      exact ⟨hsome, hc⟩
  · intro ⟨hsome, hnotP⟩
    rw [shrinkColor_apply, ite_eq_right hnotP]
    exact hsome

/-- Second part: for every `m ≤ 32` there is a coloring with exactly `m`
colored edges and no monochromatic triangle. -/
lemma exists_avoiding (m : ℕ) (hm : m ≤ 32) :
    ∃ c : EdgeColoring, c.coloredEdges.card = m ∧ ¬ c.HasMonoTriangle := by
  obtain ⟨P, hPsub, hPcard⟩ := Finset.exists_subset_card_eq
    (show 32 - m ≤ auxColoring.coloredEdges.card by rw [aux_colored_card]; lia)
  refine ⟨shrinkColoring P, ?_, ?_⟩
  · rw [shrink_coloredEdges P, Finset.card_sdiff_of_subset hPsub,
      aux_colored_card, hPcard, Nat.sub_sub_self hm]
  · rintro ⟨i, j, k, hij, hjk, hki, b, e1, e2, e3⟩
    exact aux_no_mono ⟨i, j, k, hij, hjk, hki, b,
      shrinkColor_some_of e1, shrinkColor_some_of e2, shrinkColor_some_of e3⟩

snip end

determine answer : ℕ := 33

problem imo1992_p3 :
    IsLeast {n : ℕ | ∀ c : EdgeColoring, c.coloredEdges.card = n →
      c.HasMonoTriangle} answer := by
  rw [show answer = 33 from rfl]
  constructor
  · intro c hc
    exact mono_triangle_of_colored_ge c (by lia)
  · intro m hm
    by_contra hlt
    push Not at hlt
    obtain ⟨cc, hcard, hnottri⟩ := exists_avoiding m (by lia)
    exact hnottri (hm cc hcard)

end Imo1992P3
