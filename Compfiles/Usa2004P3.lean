/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.IntervalCases
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics, .Geometry] }

/-!
# USA Mathematical Olympiad 2004, Problem 3

For what real values of k > 0 is it possible to dissect a 1 × k
rectangle into two similar but noncongruent polygons?
-/

namespace Usa2004P3

open Complex Topology

snip begin

/-!
## Definitions

We formalize dissections of the rectangle `[0,1] × [0,k]` (identified with the
complex plane) into two polygons. A polygon is described by the cyclically
ordered list of its vertices. A dissection into two polygons is given by a
polygonal chain `B` (the interface between the two pieces) whose endpoints lie
on the boundary of the rectangle, together with the two boundary arcs between
the endpoints. The boundary arcs are described by parameter lists (see
`sqParam`). The two polygons are required to be similar (via an explicit
similarity of the plane, possibly orientation-reversing, composed with a cyclic
rotation of the vertex list) but not congruent.
-/

/-- The corners of the rectangle `[0,1] × [0,k]`, indexed periodically (with
period 4) by `ℤ`, in counterclockwise order starting from the origin. -/
noncomputable def corner (k : ℝ) (c : ℤ) : ℂ :=
  if c % 4 = 0 then 0
  else if c % 4 = 1 then 1
  else if c % 4 = 2 then 1 + (k : ℂ) * I
  else (k : ℂ) * I

/-- The counterclockwise parametrization of the boundary of the rectangle
`[0,1] × [0,k]`, where each side has parameter length `1`. -/
noncomputable def sqParam (k : ℝ) (t : ℝ) : ℂ :=
  corner k ⌊t⌋ + (t - (⌊t⌋ : ℝ)) • (corner k (⌊t⌋ + 1) - corner k ⌊t⌋)

/-- A polygonal chain along the boundary of a rectangle, described by a strictly
increasing list of parameters from `a` to `b` (see `sqParam`). The conditions
ensure that the chain travels along the boundary (each edge stays on one side),
that it has no redundant vertices (every interior vertex is a corner), and that
it passes through every corner strictly between `a` and `b`. -/
structure BoundaryArc (a b : ℝ) where
  s : List ℝ
  hne : s ≠ []
  hhead : s.head hne = a
  hlast : s.getLast hne = b
  hmono : s.IsChain (· < ·)
  hside : s.IsChain fun x y => ∃ c : ℤ, (c : ℝ) ≤ x ∧ y ≤ c + 1
  hint : ∀ x ∈ s, x ≠ a → x ≠ b → ∃ c : ℤ, x = (c : ℝ)
  hcover : ∀ c : ℤ, a < (c : ℝ) → (c : ℝ) < b → (c : ℝ) ∈ s

/-- The points of a boundary arc of the rectangle `[0,1] × [0,k]`. -/
noncomputable def BoundaryArc.points (k : ℝ) {a b : ℝ} (A : BoundaryArc a b) : List ℂ :=
  A.s.map (sqParam k)

/-- The consecutive differences of a list of real numbers. -/
def chainGaps : List ℝ → List ℝ
  | [] => []
  | [_] => []
  | x :: y :: rest => (y - x) :: chainGaps (y :: rest)

/-- The lengths of the consecutive edges of a polygonal chain. -/
noncomputable def chainEdges : List ℂ → List ℝ
  | [] => []
  | [_] => []
  | a :: b :: rest => ‖a - b‖ :: chainEdges (b :: rest)

/-- The lengths of the edges of a polygonal cycle (including the closing edge
from the last vertex back to the first). -/
noncomputable def edgeLengths (V : List ℂ) : List ℝ :=
  chainEdges V ++ (if V = [] then [] else [‖V.getLast! - V.head!‖])

/-- The maximum of a list of real numbers, with default value `0`. -/
def maxE (l : List ℝ) : ℝ := l.foldl max 0

/-- Two polygonal cycles are similar if one is a cyclic rotation of the image of
the other under a similarity of the plane (possibly orientation-reversing). -/
def CycleSimilar (V W : List ℂ) : Prop :=
  ∃ (α β : ℂ) (m : ℕ), α ≠ 0 ∧
    (W = (V.map fun z => α * z + β).rotate m ∨
     W = (V.map fun z => α * star z + β).rotate m)

/-- Two polygonal cycles are congruent if one is a cyclic rotation of the image
of the other under an isometry of the plane. -/
def CycleCongruent (V W : List ℂ) : Prop :=
  ∃ (α β : ℂ) (m : ℕ), ‖α‖ = 1 ∧
    (W = (V.map fun z => α * z + β).rotate m ∨
     W = (V.map fun z => α * star z + β).rotate m)

/-- `Dissectable k` says that the rectangle `[0,1] × [0,k]` can be dissected
into two similar but noncongruent polygons. The dissection is given by a
polygonal chain `B` (the interface between the two pieces, whose interior
vertices lie in the interior of the rectangle) whose endpoints split the
boundary of the rectangle into two boundary arcs `A` and `C`. The two polygons
are formed by `B` together with each of the two arcs. (Since the interface of
any dissection of a polygon into two polygons is such a chain, this faithfully
models the informal notion of dissection.) -/
def Dissectable (k : ℝ) : Prop :=
  ∃ (B : List ℂ) (t₀ t₁ : ℝ) (A : BoundaryArc t₀ t₁) (C : BoundaryArc t₁ (t₀ + 4)),
    2 ≤ B.length ∧
    B.head! = sqParam k t₀ ∧
    B.getLast! = sqParam k t₁ ∧
    (∀ z ∈ B.tail.dropLast, 0 < z.re ∧ z.re < 1 ∧ 0 < z.im ∧ z.im < k) ∧
    B.IsChain (· ≠ ·) ∧
    (let P := B ++ (A.points k).reverse.tail.dropLast
     let Q := B ++ (C.points k).tail.dropLast
     CycleSimilar P Q ∧ ¬ CycleCongruent P Q)


/-! ### Basic facts about `corner` and `sqParam` -/

@[simp] lemma corner_at_zero (k : ℝ) : corner k 0 = 0 := by norm_num [corner]
@[simp] lemma corner_at_one (k : ℝ) : corner k 1 = 1 := by norm_num [corner]
@[simp] lemma corner_at_two (k : ℝ) : corner k 2 = 1 + k * I := by norm_num [corner]
@[simp] lemma corner_at_three (k : ℝ) : corner k 3 = k * I := by norm_num [corner]

lemma corner_add_four (k : ℝ) (c : ℤ) : corner k (c + 4) = corner k c := by
  have h : (c + 4) % 4 = c % 4 := by omega
  simp only [corner, h]

lemma sqParam_periodic (k : ℝ) (t : ℝ) : sqParam k (t + 4) = sqParam k t := by
  have hf : ⌊t + 4⌋ = ⌊t⌋ + 4 := by
    rw [show (4 : ℝ) = ((4 : ℤ) : ℝ) by simp, Int.floor_add_intCast]
  have h2 : (t + 4) - ((⌊t⌋ + 4 : ℤ) : ℝ) = t - (⌊t⌋ : ℝ) := by push_cast; ring
  unfold sqParam
  rw [hf, h2, corner_add_four k ⌊t⌋, show ⌊t⌋ + 4 + 1 = ⌊t⌋ + 1 + 4 from by ring,
    corner_add_four k (⌊t⌋ + 1)]

lemma sqParam_eq_on_Icc (k : ℝ) {c : ℤ} {t : ℝ} (hct : (c : ℝ) ≤ t) (htc : t ≤ c + 1) :
    sqParam k t = corner k c + (t - (c : ℝ)) • (corner k (c + 1) - corner k c) := by
  rcases eq_or_lt_of_le htc with h | h
  · subst h
    have hf : ⌊((c : ℝ) + 1)⌋ = c + 1 := by
      rw [show ((c : ℝ) + 1) = ((c + 1 : ℤ) : ℝ) by push_cast; ring, Int.floor_intCast]
    have hz : ((c : ℝ) + 1 - ((c + 1 : ℤ) : ℝ)) = 0 := by push_cast; ring
    have h1 : ((c : ℝ) + 1 - (c : ℝ)) = 1 := by ring
    simp only [sqParam, hf, hz, h1, zero_smul, one_smul, add_zero]
    exact (add_sub_cancel _ _).symm
  · have hf : ⌊t⌋ = c := Int.floor_eq_iff.2 ⟨hct, h⟩
    unfold sqParam
    rw [hf]

lemma sqParam_sub (k : ℝ) {c : ℤ} {x y : ℝ} (hx : (c : ℝ) ≤ x) (hxy : x ≤ y)
    (hy : y ≤ c + 1) :
    sqParam k y - sqParam k x = (y - x) • (corner k (c + 1) - corner k c) := by
  rw [sqParam_eq_on_Icc k hx (hxy.trans hy), sqParam_eq_on_Icc k (hx.trans hxy) hy]
  rw [show ∀ (u v w : ℂ), u + v - (u + w) = v - w from fun u v w => by ring, ← sub_smul]
  congr 1
  ring

lemma corner_one_diff_norm (c : ℤ) : ‖corner (1 : ℝ) (c + 1) - corner 1 c‖ = 1 := by
  have h0 : c % 4 = 0 ∨ c % 4 = 1 ∨ c % 4 = 2 ∨ c % 4 = 3 := by omega
  rcases h0 with h | h | h | h
  · have h' : (c + 1) % 4 = 1 := by omega
    simp [corner, h, h']
  · have h' : (c + 1) % 4 = 2 := by omega
    simp [corner, h, h']
  · have h' : (c + 1) % 4 = 3 := by omega
    simp [corner, h, h']
  · have h' : (c + 1) % 4 = 0 := by omega
    simp [corner, h, h']

/-! ### Facts about `maxE` -/

lemma le_foldl_max (l : List ℝ) (a : ℝ) : a ≤ l.foldl max a := by
  induction l generalizing a with
  | nil => exact le_rfl
  | cons b l ih => exact (le_max_left a b).trans (ih _)

lemma le_foldl_max_of_mem {l : List ℝ} {x : ℝ} (hx : x ∈ l) (a : ℝ) : x ≤ l.foldl max a := by
  induction l generalizing a with
  | nil => simp at hx
  | cons b l ih =>
    rcases List.mem_cons.1 hx with rfl | h
    · exact (le_max_right a _).trans (le_foldl_max _ _)
    · exact ih h _

lemma le_maxE {l : List ℝ} {x : ℝ} (hx : x ∈ l) : x ≤ maxE l := le_foldl_max_of_mem hx 0

lemma foldl_max_le : ∀ (l : List ℝ) (a u : ℝ), a ≤ u → (∀ x ∈ l, x ≤ u) →
    l.foldl max a ≤ u := by
  intro l
  induction l with
  | nil => intro a u ha h; exact ha
  | cons b l ih =>
    intro a u ha h
    exact ih (max a b) u (max_le ha (h b List.mem_cons_self))
      (fun x hx => h x (List.mem_cons_of_mem b hx))

lemma maxE_le {l : List ℝ} {u : ℝ} (h0 : 0 ≤ u) (h : ∀ x ∈ l, x ≤ u) : maxE l ≤ u :=
  foldl_max_le _ _ _ h0 h

lemma foldl_max_eq_max_init : ∀ (l : List ℝ) (v : ℝ), 0 ≤ v →
    l.foldl max v = max v (l.foldl max 0) := by
  intro l
  induction l with
  | nil => intro v hv; simp [max_eq_left hv]
  | cons a l ih =>
    intro v hv
    simp only [List.foldl_cons]
    rw [ih (max v a) (le_max_of_le_left hv), ih (max 0 a) (le_max_left 0 a),
      max_assoc v a (l.foldl max 0), max_assoc 0 a (l.foldl max 0),
      ← max_assoc v 0 (max a (l.foldl max 0)), max_eq_left hv]

lemma maxE_append (l₁ l₂ : List ℝ) : maxE (l₁ ++ l₂) = max (maxE l₁) (maxE l₂) := by
  unfold maxE
  rw [List.foldl_append, foldl_max_eq_max_init _ _ (le_foldl_max l₁ 0)]

lemma foldl_max_map_mul : ∀ (l : List ℝ) (ρ v : ℝ), 0 ≤ ρ → 0 ≤ v →
    (l.map (ρ * ·)).foldl max (ρ * v) = ρ * l.foldl max v := by
  intro l
  induction l with
  | nil => intro ρ v hρ hv; simp
  | cons a l ih =>
    intro ρ v hρ hv
    simp only [List.map_cons, List.foldl_cons]
    have h : max (ρ * v) (ρ * a) = ρ * max v a := (mul_max_of_nonneg v a hρ).symm
    rw [h, ih ρ (max v a) hρ (le_max_of_le_left hv)]

lemma maxE_map_mul (l : List ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ) : maxE (l.map (ρ * ·)) = ρ * maxE l := by
  unfold maxE
  have h := foldl_max_map_mul l ρ 0 hρ (le_refl 0)
  rwa [mul_zero] at h

lemma maxE_of_perm {l₁ l₂ : List ℝ} (h : List.Perm l₁ l₂) : maxE l₁ = maxE l₂ := by
  apply le_antisymm
  · exact maxE_le (le_foldl_max _ _) (fun x hx => le_maxE (h.mem_iff.1 hx))
  · exact maxE_le (le_foldl_max _ _) (fun x hx => le_maxE (h.mem_iff.2 hx))

/-! ### Facts about `chainEdges` and `edgeLengths` -/

lemma getLast!_cons_cons {α : Type*} [Inhabited α] (a b : α) (l : List α) :
    (a :: b :: l).getLast! = (b :: l).getLast! := rfl

lemma getLast!_cons_of_ne {α : Type*} [Inhabited α] (a : α) {l : List α} (hl : l ≠ []) :
    (a :: l).getLast! = l.getLast! := by
  cases l with
  | nil => exact absurd rfl hl
  | cons b l => exact getLast!_cons_cons _ _ _

lemma getLast!_snoc {α : Type*} [Inhabited α] (L : List α) (x : α) :
    (L ++ [x]).getLast! = x := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    cases L with
    | nil => rfl
    | cons b L =>
      rw [List.cons_append, List.cons_append, getLast!_cons_cons]
      exact ih

lemma getLast!_append_of_ne {α : Type*} [Inhabited α] (B E : List α) (hE : E ≠ []) :
    (B ++ E).getLast! = E.getLast! := by
  induction B with
  | nil => rfl
  | cons a B ih =>
    cases B with
    | nil =>
      cases E with
      | nil => exact absurd rfl hE
      | cons e E => rfl
    | cons b B =>
      rw [List.cons_append, List.cons_append, getLast!_cons_cons]
      exact ih

lemma head!_append_of_ne {α : Type*} [Inhabited α] (B E : List α) (hB : B ≠ []) :
    (B ++ E).head! = B.head! := by
  cases B with
  | nil => exact absurd rfl hB
  | cons a B => rfl

lemma head!_cons_tail_dropLast {α : Type*} [Inhabited α] {D : List α} (hD : 2 ≤ D.length) :
    D.head! :: D.tail.dropLast = D.dropLast := by
  cases D with
  | nil => simp at hD
  | cons d₀ D =>
    cases D with
    | nil => simp at hD
    | cons d₁ D => rfl

lemma chainEdges_append (B E : List ℂ) (hB : B ≠ []) :
    chainEdges (B ++ E) = chainEdges B ++ chainEdges (B.getLast! :: E) := by
  induction B with
  | nil => exact absurd rfl hB
  | cons b₀ B ih =>
    cases B with
    | nil => simp [chainEdges]
    | cons b₁ B =>
      have e1 : (b₀ :: b₁ :: B) ++ E = b₀ :: b₁ :: (B ++ E) := by simp [List.cons_append]
      rw [e1, chainEdges, chainEdges]
      rw [show chainEdges (b₁ :: (B ++ E)) = chainEdges ((b₁ :: B) ++ E) from by
        simp [List.cons_append]]
      rw [ih (by simp), getLast!_cons_cons]
      simp [List.cons_append]

lemma chainEdges_append_last (L : List ℂ) (e : ℂ) :
    chainEdges (L ++ [e]) = chainEdges L ++ (if L = [] then [] else [‖L.getLast! - e‖]) := by
  cases L with
  | nil => simp [chainEdges]
  | cons a L =>
    rw [if_neg (by simp), chainEdges_append _ _ (by simp)]
    cases L with
    | nil => simp [chainEdges]
    | cons b L => simp [chainEdges, List.cons_append, getLast!_cons_cons]

lemma chainEdges_map_range (f : ℕ → ℂ) (m : ℕ) :
    chainEdges ((List.range (m + 1)).map f) =
      (List.range m).map fun i => ‖f (i + 1) - f i‖ := by
  induction m with
  | zero => simp [chainEdges]
  | succ m ih =>
    have hgl : ((List.range (m + 1)).map f).getLast! = f m := by
      rw [List.range_succ, List.map_append, List.map_singleton, getLast!_snoc]
    rw [List.range_succ, List.map_append, List.map_singleton, chainEdges_append_last, ih,
      if_neg (by simp), hgl, ← norm_neg, neg_sub, List.range_succ, List.map_append,
      List.map_singleton]

lemma edgeLengths_eq (V : List ℂ) (hV : V ≠ []) :
    edgeLengths V = chainEdges V ++ [‖V.getLast! - V.head!‖] := by
  unfold edgeLengths
  rw [if_neg hV]

lemma edgeLengths_cycle (B D : List ℂ) (hB : 2 ≤ B.length) (hD : 2 ≤ D.length)
    (hhead : D.head! = B.getLast!) (hlast : D.getLast! = B.head!) :
    edgeLengths (B ++ D.tail.dropLast) = chainEdges B ++ chainEdges D := by
  have hBne : B ≠ [] := by intro h; rw [h] at hB; simp at hB
  have hDne : D ≠ [] := by intro h; rw [h] at hD; simp at hD
  have e1 : B ++ D.tail.dropLast ≠ [] := by
    intro h
    cases B with
    | nil => exact hBne rfl
    | cons b₀ B => simp at h
  have chain1 : chainEdges (B ++ D.tail.dropLast) = chainEdges B ++ chainEdges D.dropLast := by
    rw [chainEdges_append B _ hBne, ← hhead, head!_cons_tail_dropLast hD]
  rw [edgeLengths_eq _ e1, chain1, head!_append_of_ne B _ hBne]
  by_cases hE : D.tail.dropLast = []
  · -- `D` has exactly two elements; the combined cycle is just `B`.
    have hD2 : D.length = 2 := by
      have h1 : D.tail.dropLast.length = 0 := by rw [hE]; rfl
      rw [List.length_dropLast, List.length_tail] at h1
      omega
    obtain ⟨d₀, d₁, rfl⟩ := List.length_eq_two.1 hD2
    have h0 : d₀ = B.getLast! := hhead
    have h1 : d₁ = B.head! := hlast
    rw [show ([d₀, d₁] : List ℂ).tail.dropLast = [] from rfl, List.append_nil,
      show ([d₀, d₁] : List ℂ).dropLast = [d₀] from rfl]
    simp only [chainEdges, List.append_nil]
    rw [h0, h1]
  · -- the closing edge of the combined cycle is the last edge of `D`.
    have g1 : (B ++ D.tail.dropLast).getLast! = D.dropLast.getLast! := by
      rw [getLast!_append_of_ne B _ hE, ← head!_cons_tail_dropLast hD,
        getLast!_cons_of_ne _ hE]
    rw [g1, ← hlast]
    have hDl : D.dropLast ≠ [] := by
      intro h
      have h2 : D.dropLast.length = 0 := by rw [h]; rfl
      rw [List.length_dropLast] at h2
      omega
    have e2 : D = D.dropLast ++ [D.getLast!] := by
      have e3 : D.getLast! = D.getLast hDne := by
        cases D with
        | nil => exact absurd rfl hDne
        | cons a as => rfl
      rw [e3]
      exact (List.dropLast_append_getLast hDne).symm
    have e3 : chainEdges D = chainEdges D.dropLast ++ [‖D.dropLast.getLast! - D.getLast!‖] := by
      conv_lhs => rw [e2]
      rw [chainEdges_append_last, if_neg hDl]
    rw [e3, ← List.append_assoc]


/-! ### More list helpers -/

lemma head!_map {α β : Type*} [Inhabited α] [Inhabited β] (f : α → β) {l : List α}
    (hl : l ≠ []) : (l.map f).head! = f l.head! := by
  cases l with
  | nil => exact absurd rfl hl
  | cons a l => rfl

lemma getLast!_map {α β : Type*} [Inhabited α] [Inhabited β] (f : α → β) {l : List α}
    (hl : l ≠ []) : (l.map f).getLast! = f l.getLast! := by
  cases l with
  | nil => exact absurd rfl hl
  | cons a l =>
    induction l generalizing a with
    | nil => rfl
    | cons b l ih =>
      rw [List.map_cons, List.map_cons, getLast!_cons_cons, getLast!_cons_cons]
      exact ih b (by simp)

lemma getLast!_eq_getLast {α : Type*} [Inhabited α] {l : List α} (h : l ≠ []) :
    l.getLast! = l.getLast h := by
  cases l with
  | nil => exact absurd rfl h
  | cons a as => rfl

lemma head!_eq_head {α : Type*} [Inhabited α] {l : List α} (h : l ≠ []) :
    l.head! = l.head h := by
  cases l with
  | nil => exact absurd rfl h
  | cons a as => rfl

lemma head!_reverse {α : Type*} [Inhabited α] {l : List α} (hl : l ≠ []) :
    l.reverse.head! = l.getLast! := by
  induction l with
  | nil => exact absurd rfl hl
  | cons a l ih =>
    cases l with
    | nil => rfl
    | cons b l =>
      rw [List.reverse_cons, head!_append_of_ne _ _ (by simp), getLast!_cons_cons]
      exact ih (by simp)

lemma IsChain.head!_rel_of_mem_tail {R : ℝ → ℝ → Prop}
    (ht : ∀ {a b c : ℝ}, R a b → R b c → R a c) {l : List ℝ} (hc : l.IsChain R) {x : ℝ}
    (hx : x ∈ l.tail) : R l.head! x := by
  cases l with
  | nil => simp at hx
  | cons a l =>
    rw [List.tail_cons] at hx
    induction l generalizing a with
    | nil => simp at hx
    | cons b l ih =>
      have hab : R a b := (List.isChain_cons_cons.1 hc).1
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hab
      · exact ht hab (ih b (List.IsChain.tail hc) hx)

lemma IsChain.getLast!_rel_of_mem_dropLast {R : ℝ → ℝ → Prop}
    (ht : ∀ {a b c : ℝ}, R a b → R b c → R a c) {l : List ℝ} (hc : l.IsChain R) {x : ℝ}
    (hx : x ∈ l.dropLast) : R x l.getLast! := by
  have h1 : l.dropLast = l.reverse.tail.reverse := by
    rw [← List.reverse_reverse l.dropLast, ← List.tail_reverse]
  rw [h1, List.mem_reverse] at hx
  have hc2 : l.reverse.IsChain (fun a b => R b a) := List.isChain_reverse.2 hc
  have h2 := IsChain.head!_rel_of_mem_tail (R := fun a b => R b a) (fun h h' => ht h' h) hc2 hx
  have hl : l ≠ [] := by
    intro hnl
    rw [hnl] at hx
    simp at hx
  rwa [head!_reverse hl] at h2

lemma IsChain.nodup_of_lt {l : List ℝ} (hc : l.IsChain (· < ·)) : l.Nodup := by
  have h := hc.pairwise
  clear hc
  induction h with
  | nil => exact List.nodup_nil
  | cons h1 h2 ih =>
    exact List.nodup_cons.2 ⟨fun hx => (h1 _ hx).ne rfl, ih⟩

lemma mem_tail_of_ne_head! {α : Type*} [Inhabited α] {l : List α} {x : α} (hx : x ∈ l)
    (hxn : x ≠ l.head!) : x ∈ l.tail := by
  cases l with
  | nil => simp at hx
  | cons a l =>
    rcases List.mem_cons.1 hx with rfl | hx
    · exact absurd rfl hxn
    · exact hx

lemma mem_dropLast_of_ne_getLast! {α : Type*} [Inhabited α] {l : List α} {x : α} (hx : x ∈ l)
    (hxn : x ≠ l.getLast!) : x ∈ l.dropLast := by
  induction l with
  | nil => simp at hx
  | cons a l ih =>
    cases l with
    | nil =>
      rcases List.mem_cons.1 hx with rfl | hx
      · exact absurd rfl hxn
      · simp at hx
    | cons b l =>
      rw [show (a :: b :: l).dropLast = a :: (b :: l).dropLast from rfl]
      rcases List.mem_cons.1 hx with rfl | hx
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem a (ih hx (by rwa [getLast!_cons_cons] at hxn))

/-! ### Facts about `BoundaryArc` -/

lemma BoundaryArc.length_points (k : ℝ) {a b : ℝ} (A : BoundaryArc a b) :
    (A.points k).length = A.s.length := by rw [BoundaryArc.points, List.length_map]

lemma BoundaryArc.head!_points (k : ℝ) {a b : ℝ} (A : BoundaryArc a b) :
    (A.points k).head! = sqParam k a := by
  rw [BoundaryArc.points, head!_map _ A.hne, head!_eq_head A.hne, A.hhead]

lemma BoundaryArc.getLast!_points (k : ℝ) {a b : ℝ} (A : BoundaryArc a b) :
    (A.points k).getLast! = sqParam k b := by
  rw [BoundaryArc.points, getLast!_map _ A.hne, getLast!_eq_getLast A.hne, A.hlast]

lemma gap_mem_bounds_aux {l : List ℝ} (hmono : l.IsChain (· < ·))
    (hside : l.IsChain fun x y => ∃ c : ℤ, (c : ℝ) ≤ x ∧ y ≤ c + 1) :
    ∀ x ∈ chainGaps l, 0 < x ∧ x ≤ 1 := by
  induction l with
  | nil => intro x hx; simp [chainGaps] at hx
  | cons u l ih =>
    cases l with
    | nil => intro x hx; simp [chainGaps] at hx
    | cons v l =>
      intro x hx
      simp only [chainGaps, List.mem_cons] at hx
      rcases hx with rfl | hx
      · obtain ⟨c, hc1, hc2⟩ := (List.isChain_cons_cons.1 hside).1
        have hm : u < v := (List.isChain_cons_cons.1 hmono).1
        exact ⟨by linarith, by linarith⟩
      · exact ih (List.IsChain.tail hmono) (List.IsChain.tail hside) x hx

lemma BoundaryArc.gap_mem_bounds {a b : ℝ} (A : BoundaryArc a b) :
    ∀ x ∈ chainGaps A.s, 0 < x ∧ x ≤ 1 := gap_mem_bounds_aux A.hmono A.hside

lemma chainEdges_points_one_aux {l : List ℝ} (hmono : l.IsChain (· < ·))
    (hside : l.IsChain fun x y => ∃ c : ℤ, (c : ℝ) ≤ x ∧ y ≤ c + 1) :
    chainEdges (l.map (sqParam 1)) = chainGaps l := by
  induction l with
  | nil => rfl
  | cons u l ih =>
    cases l with
    | nil => rfl
    | cons v l =>
      have hm : u < v := (List.isChain_cons_cons.1 hmono).1
      obtain ⟨c, hc1, hc2⟩ := (List.isChain_cons_cons.1 hside).1
      rw [List.map_cons, List.map_cons, chainEdges, chainGaps, norm_sub_rev,
        sqParam_sub 1 hc1 (le_of_lt hm) hc2, norm_smul, corner_one_diff_norm, mul_one,
        Real.norm_eq_abs, abs_of_pos (by linarith)]
      congr 1
      exact ih (List.IsChain.tail hmono) (List.IsChain.tail hside)

lemma BoundaryArc.chainEdges_points_one {a b : ℝ} (A : BoundaryArc a b) :
    chainEdges (A.points 1) = chainGaps A.s := chainEdges_points_one_aux A.hmono A.hside

/-- The integers strictly between two real numbers. -/
noncomputable def intBetween (a b : ℝ) : Finset ℤ := Finset.Ico (⌊a⌋ + 1) ⌈b⌉

lemma mem_intBetween {a b : ℝ} {c : ℤ} :
    c ∈ intBetween a b ↔ (a : ℝ) < c ∧ (c : ℝ) < b := by
  unfold intBetween
  rw [Finset.mem_Ico]
  constructor
  · rintro ⟨h1, h2⟩
    have ha : (⌊a⌋ + 1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast h1
    have hb : c ≤ ⌈b⌉ - 1 := by omega
    have haf : a < (⌊a⌋ + 1 : ℝ) := Int.lt_floor_add_one a
    have hbc : (⌈b⌉ : ℝ) < b + 1 := Int.ceil_lt_add_one b
    have hb' : ((⌈b⌉ : ℝ) - 1) < b := by linarith
    have hcb : (c : ℝ) ≤ (⌈b⌉ - 1 : ℝ) := by exact_mod_cast hb
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩
    have h3 : ⌊a⌋ < c := Int.floor_lt.2 h1
    have h4 : (c : ℝ) < (⌈b⌉ : ℝ) := lt_of_lt_of_le h2 (Int.le_ceil b)
    exact ⟨by omega, by exact_mod_cast h4⟩

lemma card_intBetween (a b : ℝ) : (intBetween a b).card = (⌈b⌉ - ⌊a⌋ - 1).toNat := by
  unfold intBetween
  rw [Int.card_Ico]
  congr 1
  omega

open Classical in
lemma ceil_sub_floor (a : ℝ) :
    ⌈a⌉ - ⌊a⌋ = if a ∈ Set.range (Int.cast : ℤ → ℝ) then 0 else 1 := by
  by_cases ha : a ∈ Set.range (Int.cast : ℤ → ℝ)
  · rw [if_pos ha]
    obtain ⟨n, rfl⟩ := ha
    rw [Int.ceil_intCast, Int.floor_intCast, sub_self]
  · rw [if_neg ha, (Int.ceil_eq_floor_add_one_iff_notMem a).2 ha]
    omega

lemma BoundaryArc.interior_toFinset {a b : ℝ} (A : BoundaryArc a b) :
    (A.s.tail.dropLast).toFinset =
      (intBetween a b).map ⟨(Int.cast : ℤ → ℝ), fun _ _ h => by exact_mod_cast h⟩ := by
  ext x
  rw [List.mem_toFinset, Finset.mem_map]
  constructor
  · intro hx
    have hxs : x ∈ A.s := List.tail_subset _ (List.dropLast_subset _ hx)
    have hlt1 : A.s.head! < x := IsChain.head!_rel_of_mem_tail (R := (· < ·))
      (fun h h' => lt_trans h h') A.hmono (List.dropLast_subset _ hx)
    have hlt2 : x < A.s.getLast! := by
      have htail : A.s.tail ≠ [] := by
        intro h
        rw [h] at hx
        simp at hx
      have h := IsChain.getLast!_rel_of_mem_dropLast (R := (· < ·))
        (fun h₁ h₂ => lt_trans h₁ h₂) (List.IsChain.tail A.hmono) hx
      have e : A.s.tail.getLast! = A.s.getLast! := by
        obtain ⟨u, l, hs⟩ := List.exists_cons_of_ne_nil A.hne
        rw [hs] at htail ⊢
        exact (getLast!_cons_of_ne u htail).symm
      rwa [e] at h
    have hxa : x ≠ a := by
      have e1 : A.s.head! = a := by rw [head!_eq_head A.hne]; exact A.hhead
      rw [← e1]
      exact ne_of_gt hlt1
    have hxb : x ≠ b := by
      have e2 : A.s.getLast! = b := by rw [getLast!_eq_getLast A.hne]; exact A.hlast
      rw [← e2]
      exact ne_of_lt hlt2
    obtain ⟨c, rfl⟩ := A.hint x hxs hxa hxb
    refine ⟨c, ?_, rfl⟩
    rw [mem_intBetween]
    have e1 : (a : ℝ) = A.s.head! := by rw [head!_eq_head A.hne, A.hhead]
    have e2 : (b : ℝ) = A.s.getLast! := by rw [getLast!_eq_getLast A.hne, A.hlast]
    exact ⟨e1 ▸ hlt1, e2 ▸ hlt2⟩
  · intro hx
    obtain ⟨c, hc, rfl⟩ := hx
    rw [mem_intBetween] at hc
    have hcs : ((c : ℝ) ∈ A.s) := A.hcover c hc.1 hc.2
    have hca : ((c : ℝ) ≠ a) := ne_of_gt hc.1
    have hcb : ((c : ℝ) ≠ b) := ne_of_lt hc.2
    have h2 : (c : ℝ) ≠ A.s.head! := by rwa [← A.hhead, ← head!_eq_head A.hne] at hca
    have h1 : (c : ℝ) ∈ A.s.tail := mem_tail_of_ne_head! hcs h2
    have h3 : (c : ℝ) ≠ A.s.getLast! := by rwa [← A.hlast, ← getLast!_eq_getLast A.hne] at hcb
    have e : A.s.tail.getLast! = A.s.getLast! := by
      obtain ⟨u, l, hs⟩ := List.exists_cons_of_ne_nil A.hne
      rw [hs] at h1 ⊢
      cases l with
      | nil => simp at h1
      | cons v l => exact (getLast!_cons_of_ne u (by simp)).symm
    exact mem_dropLast_of_ne_getLast! h1 (by rwa [← e] at h3)

lemma BoundaryArc.head!_eq {a b : ℝ} (A : BoundaryArc a b) : A.s.head! = a := by
  rw [head!_eq_head A.hne]; exact A.hhead

lemma BoundaryArc.getLast!_eq {a b : ℝ} (A : BoundaryArc a b) : A.s.getLast! = b := by
  rw [getLast!_eq_getLast A.hne]; exact A.hlast

lemma BoundaryArc.length_eq_card_add_two {a b : ℝ} (A : BoundaryArc a b) (hab : a ≠ b) :
    A.s.length = (intBetween a b).card + 2 := by
  have hs2 : 2 ≤ A.s.length := by
    by_contra hlt
    have h1 : A.s.length ≤ 1 := by omega
    obtain ⟨u, l, hs⟩ := List.exists_cons_of_ne_nil A.hne
    rw [hs] at h1
    cases l with
    | nil =>
      have hh := A.head!_eq
      have hl := A.getLast!_eq
      rw [hs] at hh hl
      have ex : u = a := hh
      have ey : u = b := hl
      exact absurd (ex.symm.trans ey) hab
    | cons v l => simp at h1
  have h1 := BoundaryArc.interior_toFinset A
  have h2 : ((A.s.tail.dropLast).toFinset).card =
      ((intBetween a b).map ⟨(Int.cast : ℤ → ℝ), fun _ _ h => by exact_mod_cast h⟩).card :=
    congrArg Finset.card h1
  rw [List.toFinset_card_of_nodup
      (List.Sublist.nodup (List.dropLast_sublist _) (List.Nodup.tail (IsChain.nodup_of_lt A.hmono))),
    Finset.card_map] at h2
  rw [List.length_dropLast, List.length_tail] at h2
  omega

/-! ### Facts about `CycleSimilar` and `CycleCongruent` -/

lemma edgeLengths_rotate_one_perm (V : List ℂ) :
    List.Perm (edgeLengths (V.rotate 1)) (edgeLengths V) := by
  cases V with
  | nil => simp
  | cons a V =>
    rw [List.rotate_cons_succ, List.rotate_zero]
    cases V with
    | nil => simp [edgeLengths]
    | cons b tl =>
      rw [edgeLengths_eq _ (by simp), edgeLengths_eq _ (by simp), chainEdges_append_last,
        if_neg (by simp), getLast!_snoc, head!_append_of_ne _ _ (by simp)]
      simp only [chainEdges, List.cons_append]
      rw [getLast!_cons_cons]
      exact List.perm_append_singleton _ _

lemma edgeLengths_rotate_perm (V : List ℂ) (m : ℕ) :
    List.Perm (edgeLengths (V.rotate m)) (edgeLengths V) := by
  induction m generalizing V with
  | zero => rw [List.rotate_zero]
  | succ m ih =>
    rw [show m + 1 = 1 + m from by ring, ← List.rotate_rotate]
    exact (ih (V.rotate 1)).trans (edgeLengths_rotate_one_perm V)

lemma chainEdges_map_direct (α β : ℂ) (V : List ℂ) :
    chainEdges (V.map fun z => α * z + β) = (chainEdges V).map (‖α‖ * ·) := by
  induction V with
  | nil => rfl
  | cons a V ih =>
    cases V with
    | nil => rfl
    | cons b V =>
      rw [List.map_cons, List.map_cons, chainEdges]
      have e2 : chainEdges ((α * b + β) :: V.map (fun z => α * z + β)) =
          (chainEdges (b :: V)).map (‖α‖ * ·) := ih
      rw [chainEdges, List.map_cons, e2,
        show (α * a + β) - (α * b + β) = α * (a - b) from by ring, norm_mul]

lemma chainEdges_map_conj (α β : ℂ) (V : List ℂ) :
    chainEdges (V.map fun z => α * star z + β) = (chainEdges V).map (‖α‖ * ·) := by
  induction V with
  | nil => rfl
  | cons a V ih =>
    cases V with
    | nil => rfl
    | cons b V =>
      rw [List.map_cons, List.map_cons, chainEdges]
      have e2 : chainEdges ((α * star b + β) :: V.map (fun z => α * star z + β)) =
          (chainEdges (b :: V)).map (‖α‖ * ·) := ih
      rw [chainEdges, List.map_cons, e2,
        show (α * star a + β) - (α * star b + β) = α * star (a - b) from by rw [star_sub]; ring,
        norm_mul, norm_star]

lemma edgeLengths_map_direct (α β : ℂ) (V : List ℂ) :
    edgeLengths (V.map fun z => α * z + β) = (edgeLengths V).map (‖α‖ * ·) := by
  cases V with
  | nil => simp [edgeLengths, chainEdges]
  | cons a V =>
    rw [edgeLengths_eq _ (by simp), edgeLengths_eq _ (by simp), chainEdges_map_direct α β (a :: V),
      getLast!_map _ (by simp), head!_map _ (by simp),
      show (α * (a :: V).getLast! + β) - (α * (a :: V).head! + β) =
        α * ((a :: V).getLast! - (a :: V).head!) from by ring,
      norm_mul, List.map_append, List.map_singleton]

lemma edgeLengths_map_conj (α β : ℂ) (V : List ℂ) :
    edgeLengths (V.map fun z => α * star z + β) = (edgeLengths V).map (‖α‖ * ·) := by
  cases V with
  | nil => simp [edgeLengths, chainEdges]
  | cons a V =>
    rw [edgeLengths_eq _ (by simp), edgeLengths_eq _ (by simp), chainEdges_map_conj α β (a :: V),
      getLast!_map _ (by simp), head!_map _ (by simp),
      show (α * star (a :: V).getLast! + β) - (α * star (a :: V).head! + β) =
        α * star ((a :: V).getLast! - (a :: V).head!) from by rw [star_sub]; ring,
      norm_mul, norm_star, List.map_append, List.map_singleton]

lemma CycleSimilar.length_eq {V W : List ℂ} (h : CycleSimilar V W) : V.length = W.length := by
  obtain ⟨α, β, m, hα, hcase⟩ := h
  rcases hcase with rfl | rfl <;> simp [List.length_rotate, List.length_map]

lemma CycleSimilar.edgeLengths_perm {V W : List ℂ} (h : CycleSimilar V W) :
    ∃ ρ : ℝ, 0 < ρ ∧ List.Perm (edgeLengths W) ((edgeLengths V).map (ρ * ·)) := by
  obtain ⟨α, β, m, hα, hcase⟩ := h
  refine ⟨‖α‖, norm_pos_iff.2 hα, ?_⟩
  rcases hcase with rfl | rfl
  · exact (edgeLengths_rotate_perm _ _).trans (List.Perm.of_eq (edgeLengths_map_direct α β V))
  · exact (edgeLengths_rotate_perm _ _).trans (List.Perm.of_eq (edgeLengths_map_conj α β V))

lemma CycleCongruent.edgeLengths_perm {V W : List ℂ} (h : CycleCongruent V W) :
    List.Perm (edgeLengths W) (edgeLengths V) := by
  obtain ⟨α, β, m, hα, hcase⟩ := h
  rcases hcase with rfl | rfl
  · exact (edgeLengths_rotate_perm _ _).trans
      (List.Perm.of_eq (by rw [edgeLengths_map_direct, hα]; simp))
  · exact (edgeLengths_rotate_perm _ _).trans
      (List.Perm.of_eq (by rw [edgeLengths_map_conj, hα]; simp))

lemma CycleSimilar.of_direct {V W : List ℂ} {α β : ℂ} (hα : α ≠ 0) {m : ℕ}
    (h : W = (V.map fun z => α * z + β).rotate m) : CycleSimilar V W :=
  ⟨α, β, m, hα, Or.inl h⟩

lemma CycleSimilar.of_conj {V W : List ℂ} {α β : ℂ} (hα : α ≠ 0) {m : ℕ}
    (h : W = (V.map fun z => α * star z + β).rotate m) : CycleSimilar V W :=
  ⟨α, β, m, hα, Or.inr h⟩

lemma CycleSimilar.symm {V W : List ℂ} (hV : V ≠ []) (h : CycleSimilar V W) :
    CycleSimilar W V := by
  obtain ⟨α, β, m, hα, hcase⟩ := h
  have hVl : 0 < V.length := by rwa [List.length_pos_iff]
  have h3 : (m + (V.length - m % V.length)) % V.length = 0 := by
    have h4 := Nat.mod_add_div m V.length
    have h6 : m % V.length < V.length := Nat.mod_lt _ hVl
    have h5 : m + (V.length - m % V.length) = V.length * (m / V.length) + V.length := by
      omega
    rw [h5, Nat.add_mod_right, Nat.mul_mod_right]
  rcases hcase with rfl | rfl
  · refine CycleSimilar.of_direct (inv_ne_zero hα) (m := V.length - m % V.length)
      (β := -α⁻¹ * β) ?_
    have e1 : ((V.map fun z => α * z + β).rotate m).map (fun z => α⁻¹ * z + (-α⁻¹ * β)) =
        V.rotate m := by
      rw [List.map_rotate, List.map_map]
      have hf : (fun z => α⁻¹ * z + (-α⁻¹ * β)) ∘ (fun z => α * z + β) = id := by
        funext z
        simp only [Function.comp_apply, id_eq]
        rw [mul_add, ← mul_assoc, inv_mul_cancel₀ hα, one_mul]
        ring
      rw [hf]
      simp
    rw [e1, List.rotate_rotate, ← List.rotate_mod, h3, List.rotate_zero]
  · have hα' : star α ≠ 0 := by simpa using hα
    refine CycleSimilar.of_conj (inv_ne_zero hα') (m := V.length - m % V.length)
      (β := -(star α)⁻¹ * star β) ?_
    have e1 : ((V.map fun z => α * star z + β).rotate m).map
        (fun z => (star α)⁻¹ * star z + (-(star α)⁻¹ * star β)) = V.rotate m := by
      rw [List.map_rotate, List.map_map]
      have hf : (fun z => (star α)⁻¹ * star z + (-(star α)⁻¹ * star β)) ∘
          (fun z => α * star z + β) = id := by
        funext z
        simp only [Function.comp_apply, id_eq]
        rw [star_add, star_mul, star_star]
        field_simp [hα']
        ring
      rw [hf]
      simp
    rw [e1, List.rotate_rotate, ← List.rotate_mod, h3, List.rotate_zero]


/-! ### The counting argument: unit gaps -/

lemma mem_chainGaps_of_adjacent {l : List ℝ} (hc : l.IsChain (· < ·)) {x y : ℝ}
    (hx : x ∈ l) (hy : y ∈ l) (hxy : x < y) (hmid : ∀ z ∈ l, z ≤ x ∨ y ≤ z) :
    (y - x) ∈ chainGaps l := by
  induction l with
  | nil => simp at hx
  | cons u l ih =>
    cases l with
    | nil =>
      rcases List.mem_singleton.1 hx with rfl
      rcases List.mem_singleton.1 hy with rfl
      exact absurd hxy (lt_irrefl _)
    | cons v l =>
      rw [chainGaps]
      simp only [List.mem_cons]
      rcases List.mem_cons.1 hx with hx | hx
      · rcases List.mem_cons.1 hy with hy | hy
        · rw [hx] at hxy
          rw [hy] at hxy
          exact absurd hxy (lt_irrefl _)
        · rcases List.mem_cons.1 hy with hy | hy
          · rw [hx, hy]
            exact Or.inl rfl
          · have huv : u < v := (List.isChain_cons_cons.1 hc).1
            rcases hmid v (List.mem_cons_of_mem _ List.mem_cons_self) with h | h
            · rw [hx] at h
              linarith [huv]
            · have hvy : v ≤ y := le_of_lt (IsChain.head!_rel_of_mem_tail (R := (· < ·))
                    (fun h₁ h₂ => lt_trans h₁ h₂) (List.IsChain.tail hc)
                    (by rwa [List.tail_cons]))
              have h2 : y = v := le_antisymm h hvy
              rw [hx, h2]
              exact Or.inl rfl
      · have hux : u < x := IsChain.head!_rel_of_mem_tail (R := (· < ·))
          (fun h₁ h₂ => lt_trans h₁ h₂) hc (by rwa [List.tail_cons])
        have hy' : y ∈ (v :: l) := by
          rcases List.mem_cons.1 hy with hy | hy
          · rw [hy] at hxy
            linarith [hux]
          · exact hy
        exact Or.inr (ih (List.IsChain.tail hc) hx hy'
          (fun z hz => hmid z (List.mem_cons_of_mem _ hz)))

lemma unit_gap_of_singleton {l : List ℝ} (hc : l.IsChain (· < ·)) {a b c : ℝ}
    (hhead : l.head! = a) (hlast : l.getLast! = b) (hcl : c ∈ l) (ha : a < c) (hb : c < b)
    (honly : ∀ z ∈ l, z ≠ a → z ≠ b → z = c) :
    (c - a) ∈ chainGaps l := by
  cases l with
  | nil => simp at hcl
  | cons u l =>
    have hu : u = a := hhead
    rcases List.mem_cons.1 hcl with rfl | hcl
    · linarith
    · cases l with
      | nil => simp at hcl
      | cons v l =>
        have huv : u < v := (List.isChain_cons_cons.1 hc).1
        have hv : v = c := by
          have hvs : v ∈ (u :: v :: l) := List.mem_cons_of_mem _ List.mem_cons_self
          have hva : v ≠ a := by
            rw [← hu]
            exact ne_of_gt huv
          have hvb : v ≠ b := by
            intro h
            have hcl2 : c ∈ (v :: l).tail := by
              rw [List.tail_cons]
              rw [h] at hcl
              exact mem_tail_of_ne_head! hcl (ne_of_lt hb)
            have hlt : (v :: l).head! < c :=
              IsChain.head!_rel_of_mem_tail (R := (· < ·)) (fun h₁ h₂ => lt_trans h₁ h₂)
                (List.IsChain.tail hc) hcl2
            rw [h] at hlt
            have hlt' : b < c := hlt
            linarith
          exact honly v hvs hva hvb
        rw [chainGaps]
        simp only [List.mem_cons]
        rw [hv, hu]
        exact Or.inl rfl

lemma maxE_chainGaps_eq_one {a b : ℝ} (A : BoundaryArc a b) (h1 : (1 : ℝ) ∈ chainGaps A.s) :
    maxE (chainGaps A.s) = 1 := by
  apply le_antisymm
  · exact maxE_le (by norm_num) (fun x hx => (A.gap_mem_bounds x hx).2)
  · exact le_maxE h1

lemma Ico_eq_singleton (x : ℤ) : Finset.Ico (x + 1) (x + 2) = {x + 1} := by
  ext c
  simp only [Finset.mem_Ico, Finset.mem_singleton]
  omega

lemma Ico_eq_pair (x : ℤ) : Finset.Ico (x + 1) (x + 3) = {x + 1, x + 2} := by
  ext c
  simp only [Finset.mem_Ico, Finset.mem_insert, Finset.mem_singleton]
  omega

lemma getLast!_mem {α : Type*} [Inhabited α] {l : List α} (hl : l ≠ []) : l.getLast! ∈ l := by
  cases l with
  | nil => exact absurd rfl hl
  | cons a l =>
    induction l generalizing a with
    | nil => exact List.mem_cons_self
    | cons b l ih =>
      rw [getLast!_cons_cons]
      exact List.mem_cons_of_mem _ (ih b (by simp))

lemma getLast!_reverse {α : Type*} [Inhabited α] {l : List α} (hl : l ≠ []) :
    l.reverse.getLast! = l.head! := by
  rw [← head!_reverse (l := l.reverse) (by simp [hl]), List.reverse_reverse]

lemma chainEdges_reverse (l : List ℂ) : chainEdges l.reverse = (chainEdges l).reverse := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases l with
    | nil => rfl
    | cons b l =>
      rw [List.reverse_cons, chainEdges_append_last, if_neg (by simp), ih,
        getLast!_reverse (by simp), chainEdges, List.reverse_cons, norm_sub_rev,
        show (b :: l).head! = b from rfl]

lemma BoundaryArc.bounds_of_mem_interior {a b : ℝ} (A : BoundaryArc a b) {z : ℝ}
    (hz : z ∈ A.s) (hza : z ≠ a) (hzb : z ≠ b) : a < z ∧ z < b := by
  have h1 : z ∈ A.s.tail := by
    have h2 : z ≠ A.s.head! := by rwa [A.head!_eq]
    exact mem_tail_of_ne_head! hz h2
  have h3 : z < A.s.getLast! := by
    have htail : A.s.tail ≠ [] := by
      intro h
      rw [h] at h1
      simp at h1
    have e : A.s.tail.getLast! = A.s.getLast! := by
      obtain ⟨u, l, hs⟩ := List.exists_cons_of_ne_nil A.hne
      rw [hs] at htail ⊢
      exact (getLast!_cons_of_ne u htail).symm
    have h4 := IsChain.getLast!_rel_of_mem_dropLast (R := (· < ·))
      (fun h₁ h₂ => lt_trans h₁ h₂) (List.IsChain.tail A.hmono)
      (mem_dropLast_of_ne_getLast! h1 (by rwa [e, A.getLast!_eq]))
    rwa [e] at h4
  rw [A.getLast!_eq] at h3
  have h5 : A.s.head! < z := IsChain.head!_rel_of_mem_tail (R := (· < ·))
    (fun h₁ h₂ => lt_trans h₁ h₂) A.hmono h1
  rw [A.head!_eq] at h5
  exact ⟨h5, h3⟩

/-- The square cannot be dissected into two similar but noncongruent polygons:
    any such dissection would have to have the two polygons' longest sides equal,
    forcing the similarity ratio to be 1. -/
theorem not_dissectable_one : ¬ Dissectable 1 := by
  classical
  rintro ⟨B, t₀, t₁, A, C, hB2, hBh, hBl, hBint, hBne, hsim, hcong⟩
  set P := B ++ (A.points 1).reverse.tail.dropLast with hP
  set Q := B ++ (C.points 1).tail.dropLast with hQ
  have lA : (A.points 1).reverse.tail.dropLast.length = A.s.length - 2 := by
    rw [List.length_dropLast, List.length_tail, List.length_reverse,
      BoundaryArc.length_points]
    omega
  have lC : (C.points 1).tail.dropLast.length = C.s.length - 2 := by
    rw [List.length_dropLast, List.length_tail, BoundaryArc.length_points]
    omega
  have hPQlen : P.length = Q.length := hsim.length_eq
  rw [hP, hQ, List.length_append, List.length_append, lA, lC] at hPQlen
  -- Step 1: both arcs have at least two parameters.
  have cardJ34 : (intBetween t₀ (t₀ + 4)).card = 3 ∨ (intBetween t₀ (t₀ + 4)).card = 4 := by
    rw [card_intBetween]
    have h4 : (t₀ + 4 : ℝ) = t₀ + ((4 : ℤ) : ℝ) := by norm_num
    rw [h4, Int.ceil_add_intCast]
    have h5 := ceil_sub_floor t₀
    by_cases h : t₀ ∈ Set.range (Int.cast : ℤ → ℝ)
    · rw [if_pos h] at h5
      left
      omega
    · rw [if_neg h] at h5
      right
      omega
  have hAC2 : 2 ≤ A.s.length ∧ 2 ≤ C.s.length := by
    by_cases hA1 : A.s.length = 1
    · have ht : t₀ = t₁ := by
        have hh := A.head!_eq
        have hl := A.getLast!_eq
        obtain ⟨u, l, hs⟩ := List.exists_cons_of_ne_nil A.hne
        have hlu : l = [] := by
          have hx : (u :: l).length = 1 := by rw [← hs, hA1]
          simp [List.length] at hx
          exact hx
        rw [hlu] at hs
        rw [hs] at hh hl
        have e1 : u = t₀ := hh
        have e2 : u = t₁ := hl
        rw [← e1, ← e2]
      have hC : C.s.length = (intBetween t₁ (t₀ + 4)).card + 2 :=
        C.length_eq_card_add_two (by rw [← ht]; norm_num)
      have hJ : intBetween t₁ (t₀ + 4) = intBetween t₀ (t₀ + 4) := by rw [← ht]
      rw [hJ] at hC
      rcases cardJ34 with h | h
      · rw [h] at hC; omega
      · rw [h] at hC; omega
    · by_cases hC1 : C.s.length = 1
      · have ht : t₁ = t₀ + 4 := by
          have hh := C.head!_eq
          have hl := C.getLast!_eq
          obtain ⟨u, l, hs⟩ := List.exists_cons_of_ne_nil C.hne
          have hlu : l = [] := by
            have hx : (u :: l).length = 1 := by rw [← hs, hC1]
            simp [List.length] at hx
            exact hx
          rw [hlu] at hs
          rw [hs] at hh hl
          have e1 : u = t₁ := hh
          have e2 : u = t₀ + 4 := hl
          rw [← e1, ← e2]
        have hA : A.s.length = (intBetween t₀ t₁).card + 2 :=
          A.length_eq_card_add_two (by rw [ht]; norm_num)
        have hJ : intBetween t₀ t₁ = intBetween t₀ (t₀ + 4) := by rw [ht]
        rw [hJ] at hA
        rcases cardJ34 with h | h
        · rw [h] at hA; omega
        · rw [h] at hA; omega
      · exact ⟨by
          have h1 : 0 < A.s.length := by
            obtain ⟨u, l, hs⟩ := List.exists_cons_of_ne_nil A.hne
            rw [hs]
            simp
          omega, by
          have h1 : 0 < C.s.length := by
            obtain ⟨u, l, hs⟩ := List.exists_cons_of_ne_nil C.hne
            rw [hs]
            simp
          omega⟩
  obtain ⟨hA2, hC2⟩ := hAC2
  -- Step 2: t₀ < t₁ < t₀ + 4.
  have ht01 : t₀ < t₁ := by
    obtain ⟨u, l, hs⟩ := List.exists_cons_of_ne_nil A.hne
    have hl : l ≠ [] := by
      intro h
      rw [hs, h] at hA2
      simp at hA2
    have hgl : A.s.getLast! ∈ A.s.tail := by
      rw [hs, getLast!_cons_of_ne u hl, List.tail_cons]
      exact getLast!_mem hl
    have hlt := IsChain.head!_rel_of_mem_tail (R := (· < ·)) (fun h₁ h₂ => lt_trans h₁ h₂)
      A.hmono hgl
    rwa [A.head!_eq, A.getLast!_eq] at hlt
  have ht14 : t₁ < t₀ + 4 := by
    obtain ⟨u, l, hs⟩ := List.exists_cons_of_ne_nil C.hne
    have hl : l ≠ [] := by
      intro h
      rw [hs, h] at hC2
      simp at hC2
    have hgl : C.s.getLast! ∈ C.s.tail := by
      rw [hs, getLast!_cons_of_ne u hl, List.tail_cons]
      exact getLast!_mem hl
    have hlt := IsChain.head!_rel_of_mem_tail (R := (· < ·)) (fun h₁ h₂ => lt_trans h₁ h₂)
      C.hmono hgl
    rwa [C.head!_eq, C.getLast!_eq] at hlt
  -- Step 3: the two arcs have the same number of integer (corner) parameters.
  have hlenA := A.length_eq_card_add_two (ne_of_lt ht01)
  have hlenC := C.length_eq_card_add_two (ne_of_lt ht14)
  have hsAC : A.s.length = C.s.length := by omega
  have hcard : (intBetween t₀ t₁).card = (intBetween t₁ (t₀ + 4)).card := by omega
  rw [card_intBetween, card_intBetween] at hcard
  have h4 : (t₀ + 4 : ℝ) = t₀ + ((4 : ℤ) : ℝ) := by norm_num
  rw [h4, Int.ceil_add_intCast] at hcard
  have hx1 : ⌊t₀⌋ + 1 ≤ ⌈t₁⌉ := by
    have h3 : (⌊t₀⌋ : ℝ) ≤ t₀ := Int.floor_le t₀
    have h : (⌊t₀⌋ : ℝ) < (⌈t₁⌉ : ℝ) := lt_of_le_of_lt h3 (lt_of_lt_of_le ht01 (Int.le_ceil t₁))
    have h2 : ⌊t₀⌋ < ⌈t₁⌉ := by exact_mod_cast h
    omega
  have hu1 : ⌊t₁⌋ + 1 ≤ ⌈t₀⌉ + 4 := by
    have h3 : (⌊t₁⌋ : ℝ) ≤ t₁ := Int.floor_le t₁
    have h : (⌊t₁⌋ : ℝ) < (⌈t₀⌉ : ℝ) + 4 := by
      have h4' : (t₀ : ℝ) ≤ ⌈t₀⌉ := Int.le_ceil t₀
      linarith
    have h2 : ⌊t₁⌋ < ⌈t₀⌉ + 4 := by exact_mod_cast h
    omega
  have hcardZ : ⌈t₁⌉ - ⌊t₀⌋ - 1 = ⌈t₀⌉ + 4 - ⌊t₁⌋ - 1 := by
    have h1 : 0 ≤ ⌈t₁⌉ - ⌊t₀⌋ - 1 := by omega
    have h2 : 0 ≤ ⌈t₀⌉ + 4 - ⌊t₁⌋ - 1 := by omega
    omega
  have hd : ⌈t₁⌉ - ⌊t₁⌋ = 0 ∨ ⌈t₁⌉ - ⌊t₁⌋ = 1 := by
    have h := ceil_sub_floor t₁
    by_cases ht : t₁ ∈ Set.range (Int.cast : ℤ → ℝ)
    · rw [if_pos ht] at h; left; omega
    · rw [if_neg ht] at h; right; omega
  have he : ⌈t₀⌉ - ⌊t₀⌋ = 0 ∨ ⌈t₀⌉ - ⌊t₀⌋ = 1 := by
    have h := ceil_sub_floor t₀
    by_cases ht : t₀ ∈ Set.range (Int.cast : ℤ → ℝ)
    · rw [if_pos ht] at h; left; omega
    · rw [if_neg ht] at h; right; omega
  have hkey : 2 * (⌊t₁⌋ - ⌊t₀⌋) = 4 + (⌈t₀⌉ - ⌊t₀⌋) - (⌈t₁⌉ - ⌊t₁⌋) := by omega
  have hfloor : ⌊t₁⌋ = ⌊t₀⌋ + 2 := by omega
  have hfloorR : (⌊t₁⌋ : ℝ) = (⌊t₀⌋ : ℝ) + 2 := by exact_mod_cast hfloor
  have hceildiff : ⌈t₀⌉ - ⌊t₀⌋ = ⌈t₁⌉ - ⌊t₁⌋ := by omega
  -- Step 4: in each case, both arcs contain a unit gap.
  have hgapA : (1 : ℝ) ∈ chainGaps A.s := by
    rcases he with he | he
    · -- t₀ integer: then t₁ = t₀ + 2, and intBetween t₀ t₁ = {⌊t₀⌋ + 1}.
      have hd0 : ⌈t₁⌉ - ⌊t₁⌋ = 0 := by omega
      have ht0i : (⌊t₀⌋ : ℝ) = t₀ := by
        have h3 : ⌈t₀⌉ = ⌊t₀⌋ := by omega
        have h2 : t₀ ≤ (⌊t₀⌋ : ℝ) := h3 ▸ Int.le_ceil t₀
        exact le_antisymm (Int.floor_le t₀) h2
      have ht1i : (⌊t₁⌋ : ℝ) = t₁ := by
        have h3 : ⌈t₁⌉ = ⌊t₁⌋ := by omega
        have h2 : t₁ ≤ (⌊t₁⌋ : ℝ) := h3 ▸ Int.le_ceil t₁
        exact le_antisymm (Int.floor_le t₁) h2
      have ht1v : t₁ = (⌊t₀⌋ : ℝ) + 2 := by linarith [ht1i, hfloorR]
      have hJ1 : intBetween t₀ t₁ = {⌊t₀⌋ + 1} := by
        unfold intBetween
        have hc1 : ⌈t₁⌉ = ⌊t₀⌋ + 2 := by omega
        rw [hc1, Ico_eq_singleton]
      have hcl : ((⌊t₀⌋ + 1 : ℤ) : ℝ) ∈ A.s := by
        apply A.hcover (⌊t₀⌋ + 1)
        · push_cast
          linarith [ht0i]
        · push_cast
          linarith [ht1v]
      have h1 : (1 : ℝ) = ((⌊t₀⌋ + 1 : ℤ) : ℝ) - t₀ := by
        push_cast
        linarith [ht0i]
      rw [h1]
      exact unit_gap_of_singleton A.hmono A.head!_eq A.getLast!_eq hcl
        (by push_cast; linarith [ht0i]) (by push_cast; linarith [ht1v])
        (fun z hz hza hzb => by
          obtain ⟨c', rfl⟩ := A.hint z hz hza hzb
          have hb := A.bounds_of_mem_interior hz hza hzb
          have : c' ∈ intBetween t₀ t₁ := mem_intBetween.2 hb
          rw [hJ1] at this
          have h6 : c' = ⌊t₀⌋ + 1 := Finset.mem_singleton.1 this
          rw [h6])
    · -- t₀ non-integer: then ⌈t₀⌉ = ⌊t₀⌋ + 1, ⌊t₁⌋ = ⌊t₀⌋ + 2, ⌈t₁⌉ = ⌊t₀⌋ + 3.
      have hd1 : ⌈t₁⌉ - ⌊t₁⌋ = 1 := by omega
      have ht0ni : (⌊t₀⌋ : ℝ) < t₀ := by
        have h5 : ⌈t₀⌉ = ⌊t₀⌋ + 1 := by omega
        exact Int.floor_lt_self_iff.2 ((Int.ceil_eq_floor_add_one_iff_notMem t₀).1 h5)
      have ht0lt : t₀ < (⌊t₀⌋ : ℝ) + 1 := Int.lt_floor_add_one t₀
      have ht1gt : (⌊t₁⌋ : ℝ) < t₁ := by
        have h5 : ⌈t₁⌉ = ⌊t₁⌋ + 1 := by omega
        exact Int.floor_lt_self_iff.2 ((Int.ceil_eq_floor_add_one_iff_notMem t₁).1 h5)
      have hceil1 : ⌈t₁⌉ = ⌊t₀⌋ + 3 := by omega
      have hJ1 : intBetween t₀ t₁ = {⌊t₀⌋ + 1, ⌊t₀⌋ + 2} := by
        unfold intBetween
        rw [hceil1, Ico_eq_pair]
      have hcl1 : ((⌊t₀⌋ + 1 : ℤ) : ℝ) ∈ A.s := by
        apply A.hcover (⌊t₀⌋ + 1)
        · push_cast
          linarith [ht0lt]
        · push_cast
          linarith [hfloorR, ht1gt]
      have hcl2 : ((⌊t₀⌋ + 2 : ℤ) : ℝ) ∈ A.s := by
        apply A.hcover (⌊t₀⌋ + 2)
        · push_cast
          linarith [ht0lt]
        · push_cast
          linarith [hfloorR, ht1gt]
      have h1 : (1 : ℝ) = ((⌊t₀⌋ + 2 : ℤ) : ℝ) - ((⌊t₀⌋ + 1 : ℤ) : ℝ) := by
        push_cast; ring
      rw [h1]
      exact mem_chainGaps_of_adjacent A.hmono hcl1 hcl2 (by push_cast; norm_num)
        (fun z hz => by
          by_cases hza : z = t₀
          · left
            rw [hza]
            push_cast
            linarith [ht0lt]
          · by_cases hzb : z = t₁
            · right
              rw [hzb]
              push_cast
              linarith [hfloorR, ht1gt]
            · obtain ⟨c', rfl⟩ := A.hint z hz hza hzb
              have hb := A.bounds_of_mem_interior hz hza hzb
              have : c' ∈ intBetween t₀ t₁ := mem_intBetween.2 hb
              rw [hJ1] at this
              rcases Finset.mem_insert.1 this with h6 | h6
              · left
                rw [h6]
              · right
                rw [Finset.mem_singleton.1 h6])
  have hgapC : (1 : ℝ) ∈ chainGaps C.s := by
    rcases he with he | he
    · have hd0 : ⌈t₁⌉ - ⌊t₁⌋ = 0 := by omega
      have ht0i : (⌊t₀⌋ : ℝ) = t₀ := by
        have h3 : ⌈t₀⌉ = ⌊t₀⌋ := by omega
        have h2 : t₀ ≤ (⌊t₀⌋ : ℝ) := h3 ▸ Int.le_ceil t₀
        exact le_antisymm (Int.floor_le t₀) h2
      have ht1i : (⌊t₁⌋ : ℝ) = t₁ := by
        have h3 : ⌈t₁⌉ = ⌊t₁⌋ := by omega
        have h2 : t₁ ≤ (⌊t₁⌋ : ℝ) := h3 ▸ Int.le_ceil t₁
        exact le_antisymm (Int.floor_le t₁) h2
      have ht1v : t₁ = (⌊t₀⌋ : ℝ) + 2 := by linarith [ht1i, hfloorR]
      have ht04v : t₀ + 4 = (⌊t₀⌋ : ℝ) + 4 := by linarith [ht0i]
      have hJ2 : intBetween t₁ (t₀ + 4) = {⌊t₀⌋ + 3} := by
        unfold intBetween
        have hf1 : ⌊t₁⌋ + 1 = ⌊t₀⌋ + 3 := by omega
        have hc2 : ⌈t₀ + 4⌉ = ⌊t₀⌋ + 4 := by
          rw [h4, Int.ceil_add_intCast]
          omega
        rw [hf1, hc2]
        ext c
        simp only [Finset.mem_Ico, Finset.mem_singleton]
        omega
      have hcl : ((⌊t₀⌋ + 3 : ℤ) : ℝ) ∈ C.s := by
        apply C.hcover (⌊t₀⌋ + 3)
        · push_cast
          linarith [ht1v]
        · push_cast
          linarith [ht04v]
      have h1 : (1 : ℝ) = ((⌊t₀⌋ + 3 : ℤ) : ℝ) - t₁ := by
        push_cast
        linarith [ht1v]
      rw [h1]
      exact unit_gap_of_singleton C.hmono C.head!_eq C.getLast!_eq hcl
        (by push_cast; linarith [ht1v]) (by push_cast; linarith [ht04v])
        (fun z hz hza hzb => by
          obtain ⟨c', rfl⟩ := C.hint z hz hza hzb
          have hb := C.bounds_of_mem_interior hz hza hzb
          have : c' ∈ intBetween t₁ (t₀ + 4) := mem_intBetween.2 hb
          rw [hJ2] at this
          have h6 : c' = ⌊t₀⌋ + 3 := Finset.mem_singleton.1 this
          rw [h6])
    · have hd1 : ⌈t₁⌉ - ⌊t₁⌋ = 1 := by omega
      have ht0ni : (⌊t₀⌋ : ℝ) < t₀ := by
        have h5 : ⌈t₀⌉ = ⌊t₀⌋ + 1 := by omega
        exact Int.floor_lt_self_iff.2 ((Int.ceil_eq_floor_add_one_iff_notMem t₀).1 h5)
      have ht1gt : (⌊t₁⌋ : ℝ) < t₁ := by
        have h5 : ⌈t₁⌉ = ⌊t₁⌋ + 1 := by omega
        exact Int.floor_lt_self_iff.2 ((Int.ceil_eq_floor_add_one_iff_notMem t₁).1 h5)
      have h7 : t₁ < (⌊t₁⌋ : ℝ) + 1 := Int.lt_floor_add_one t₁
      have hJ2 : intBetween t₁ (t₀ + 4) = {⌊t₀⌋ + 3, ⌊t₀⌋ + 4} := by
        unfold intBetween
        have hf1 : ⌊t₁⌋ + 1 = ⌊t₀⌋ + 3 := by omega
        have hc2 : ⌈t₀ + 4⌉ = ⌊t₀⌋ + 5 := by
          rw [h4, Int.ceil_add_intCast]
          omega
        rw [hf1, hc2]
        ext c
        simp only [Finset.mem_Ico, Finset.mem_insert, Finset.mem_singleton]
        omega
      have hcl1 : ((⌊t₀⌋ + 3 : ℤ) : ℝ) ∈ C.s := by
        apply C.hcover (⌊t₀⌋ + 3)
        · push_cast
          linarith [hfloorR, h7]
        · push_cast
          linarith [ht0ni]
      have hcl2 : ((⌊t₀⌋ + 4 : ℤ) : ℝ) ∈ C.s := by
        apply C.hcover (⌊t₀⌋ + 4)
        · push_cast
          linarith [hfloorR, h7]
        · push_cast
          linarith [ht0ni]
      have h1 : (1 : ℝ) = ((⌊t₀⌋ + 4 : ℤ) : ℝ) - ((⌊t₀⌋ + 3 : ℤ) : ℝ) := by
        push_cast; ring
      rw [h1]
      exact mem_chainGaps_of_adjacent C.hmono hcl1 hcl2 (by push_cast; norm_num)
        (fun z hz => by
          by_cases hza : z = t₁
          · left
            rw [hza]
            push_cast
            linarith [hfloorR, h7]
          · by_cases hzb : z = t₀ + 4
            · right
              rw [hzb]
              push_cast
              linarith [ht0ni]
            · obtain ⟨c', rfl⟩ := C.hint z hz hza hzb
              have hb := C.bounds_of_mem_interior hz hza hzb
              have : c' ∈ intBetween t₁ (t₀ + 4) := mem_intBetween.2 hb
              rw [hJ2] at this
              rcases Finset.mem_insert.1 this with h6 | h6
              · left
                rw [h6]
              · right
                rw [Finset.mem_singleton.1 h6])
  -- Step 5: the longest edges of the two polygons coincide.
  have hmA : maxE (chainGaps A.s) = 1 := maxE_chainGaps_eq_one A hgapA
  have hmC : maxE (chainGaps C.s) = 1 := maxE_chainGaps_eq_one C hgapC
  have hPc : edgeLengths P = chainEdges B ++ chainEdges ((A.points 1).reverse) := by
    rw [hP]
    exact edgeLengths_cycle B ((A.points 1).reverse) hB2
      (by rw [List.length_reverse, BoundaryArc.length_points]; exact hA2)
      (by
        have h1 : A.points 1 ≠ [] := fun h => A.hne (by
          rw [BoundaryArc.points] at h
          rw [List.map_eq_nil_iff] at h
          exact h)
        rw [head!_reverse h1, A.getLast!_points, hBl])
      (by
        have h1 : A.points 1 ≠ [] := fun h => A.hne (by
          rw [BoundaryArc.points] at h
          rw [List.map_eq_nil_iff] at h
          exact h)
        rw [getLast!_reverse h1, A.head!_points, hBh])
  have hQc : edgeLengths Q = chainEdges B ++ chainEdges (C.points 1) := by
    rw [hQ]
    exact edgeLengths_cycle B (C.points 1) hB2 (by rw [BoundaryArc.length_points]; exact hC2)
      (by rw [C.head!_points, hBl]) (by rw [C.getLast!_points, sqParam_periodic, hBh])
  have hmP : maxE (edgeLengths P) = max (maxE (chainEdges B)) 1 := by
    rw [hPc, maxE_append, chainEdges_reverse,
      maxE_of_perm (List.reverse_perm _), A.chainEdges_points_one, hmA]
  have hmQ : maxE (edgeLengths Q) = max (maxE (chainEdges B)) 1 := by
    rw [hQc, maxE_append, C.chainEdges_points_one, hmC]
  -- Step 6: the similarity ratio is 1, contradiction.
  obtain ⟨α, β, m, hα, hcase⟩ := hsim
  have hρ : 0 < ‖α‖ := norm_pos_iff.2 hα
  have hperm : List.Perm (edgeLengths Q) ((edgeLengths P).map (‖α‖ * ·)) := by
    rcases hcase with hcase | hcase
    · rw [hcase]
      exact (edgeLengths_rotate_perm _ _).trans (List.Perm.of_eq (edgeLengths_map_direct α β P))
    · rw [hcase]
      exact (edgeLengths_rotate_perm _ _).trans (List.Perm.of_eq (edgeLengths_map_conj α β P))
  have heq : maxE (edgeLengths Q) = ‖α‖ * maxE (edgeLengths P) := by
    rw [maxE_of_perm hperm, maxE_map_mul _ hρ.le]
  rw [hmP, hmQ] at heq
  have hM : 0 < max (maxE (chainEdges B)) 1 := by
    rw [max_comm]
    exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hρα : ‖α‖ = 1 := by
    have h1 : (1 - ‖α‖) * max (maxE (chainEdges B)) 1 = 0 := by linarith [heq]
    rcases mul_eq_zero.1 h1 with h2 | h2
    · linarith
    · exact absurd h2 (ne_of_gt hM)
  exact hcong ⟨α, β, m, hρα, hcase⟩


/-! ### The staircase construction: partial sums and the aspect-ratio equation -/

/-- Sum of even powers `r² + r⁴ + ⋯ + r^{2j}`. -/
noncomputable def xsum (r : ℝ) (j : ℕ) : ℝ := ∑ i ∈ Finset.range j, r ^ (2 * i + 2)

/-- Sum of odd powers `r³ + r⁵ + ⋯ + r^{2j+1}`. -/
noncomputable def ysum (r : ℝ) (j : ℕ) : ℝ := ∑ i ∈ Finset.range j, r ^ (2 * i + 3)

/-- Sum of odd powers `r + r³ + ⋯ + r^{2n-1}` (the height of the staircase). -/
noncomputable def Hsum (r : ℝ) (n : ℕ) : ℝ := ∑ i ∈ Finset.range n, r ^ (2 * i + 1)

lemma xsum_succ (r : ℝ) (j : ℕ) : xsum r (j + 1) = xsum r j + r ^ (2 * j + 2) :=
  Finset.sum_range_succ _ _

lemma ysum_succ (r : ℝ) (j : ℕ) : ysum r (j + 1) = ysum r j + r ^ (2 * j + 3) :=
  Finset.sum_range_succ _ _

lemma ysum_eq_mul_xsum (r : ℝ) (j : ℕ) : ysum r j = r * xsum r j := by
  rw [ysum, xsum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma xsum_eq_mul_Hsum (r : ℝ) (n : ℕ) : xsum r n = r * Hsum r n := by
  rw [xsum, Hsum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma Hsum_eq_add_ysum (r : ℝ) {n : ℕ} (hn : 0 < n) : Hsum r n = r + ysum r (n - 1) := by
  cases n with
  | zero => omega
  | succ n =>
    simp only [Hsum, ysum]
    rw [Finset.sum_range_succ']
    have h2 : r ^ (2 * 0 + 1) = r := by ring
    rw [h2, add_comm (∑ k ∈ Finset.range n, r ^ (2 * (k + 1) + 1)) r]
    congr 1

lemma xsum_nonneg {r : ℝ} (hr : 1 ≤ r) (j : ℕ) : 0 ≤ xsum r j :=
  Finset.sum_nonneg fun i _ => by positivity

lemma ysum_nonneg {r : ℝ} (hr : 1 ≤ r) (j : ℕ) : 0 ≤ ysum r j :=
  Finset.sum_nonneg fun i _ => by positivity

lemma Hsum_pos {r : ℝ} (hr : 0 < r) {n : ℕ} (hn : 0 < n) : 0 < Hsum r n :=
  Finset.sum_pos (fun i _ => pow_pos hr _) (Finset.nonempty_range_iff.2 (by omega))

lemma xsum_strictMono {r : ℝ} (hr : 1 < r) : StrictMono (xsum r) := by
  intro a b hab
  have h1 : xsum r b - xsum r a = ∑ i ∈ Finset.Ico a b, r ^ (2 * i + 2) :=
    (Finset.sum_Ico_eq_sub _ (le_of_lt hab)).symm
  have h2 : 0 < ∑ i ∈ Finset.Ico a b, r ^ (2 * i + 2) := by
    apply Finset.sum_pos (fun i _ => by positivity)
    exact ⟨a, Finset.mem_Ico.2 ⟨le_refl a, hab⟩⟩
  have h3 : 0 ≤ xsum r a := xsum_nonneg (le_of_lt hr) a
  linarith

lemma ysum_strictMono {r : ℝ} (hr : 1 < r) : StrictMono (ysum r) := by
  intro a b hab
  have h1 : ysum r b - ysum r a = ∑ i ∈ Finset.Ico a b, r ^ (2 * i + 3) :=
    (Finset.sum_Ico_eq_sub _ (le_of_lt hab)).symm
  have h2 : 0 < ∑ i ∈ Finset.Ico a b, r ^ (2 * i + 3) := by
    apply Finset.sum_pos (fun i _ => by positivity)
    exact ⟨a, Finset.mem_Ico.2 ⟨le_refl a, hab⟩⟩
  have h3 : 0 ≤ ysum r a := ysum_nonneg (le_of_lt hr) a
  linarith

@[simp] lemma xsum_zero (r : ℝ) : xsum r 0 = 0 := by simp [xsum]
@[simp] lemma ysum_zero (r : ℝ) : ysum r 0 = 0 := by simp [ysum]

/-- For every `n ≥ 1` and every `k > 1 + 1/n` there is some `r > 1` for which the
staircase rectangle has aspect ratio exactly `k`. -/
lemma exists_ratio {n : ℕ} (hn : 0 < n) {k : ℝ} (hk : 1 + 1 / (n : ℝ) < k) :
    ∃ r : ℝ, 1 < r ∧ (1 + xsum r n) / Hsum r n = k := by
  have hHpos : ∀ r : ℝ, 1 ≤ r → 0 < Hsum r n := fun r hr => Hsum_pos (by linarith) hn
  have hH1 : Hsum 1 n = (n : ℝ) := by simp [Hsum]
  have hf_eq : ∀ r : ℝ, 1 ≤ r → (1 + xsum r n) / Hsum r n = r + 1 / Hsum r n := by
    intro r hr
    rw [xsum_eq_mul_Hsum]
    have h := (hHpos r hr).ne'
    field_simp
    ring
  have hxs : Continuous fun r => xsum r n := by
    unfold xsum
    exact continuous_finsetSum _ (fun i _ => continuous_pow _)
  have hHs : Continuous fun r => Hsum r n := by
    unfold Hsum
    exact continuous_finsetSum _ (fun i _ => continuous_pow _)
  have hcont : ∀ r : ℝ, 1 ≤ r → ContinuousAt (fun x => (1 + xsum x n) / Hsum x n) r := by
    intro r hr
    have h1 : ContinuousAt (fun x => 1 + xsum x n) r := continuousAt_const.add hxs.continuousAt
    exact h1.div hHs.continuousAt (hHpos r hr).ne'
  have hf1 : (1 + xsum 1 n) / Hsum 1 n = 1 + 1 / (n : ℝ) := by
    have hx1 : xsum 1 n = (n : ℝ) := by simp [xsum]
    have hnn : (n : ℝ) ≠ 0 := (Nat.cast_pos.2 hn).ne'
    rw [hx1, hH1]
    field_simp
    ring
  have htend : Filter.Tendsto (fun x => (1 + xsum x n) / Hsum x n) (𝓝[(Set.Ioi 1)] (1 : ℝ))
      (𝓝 (1 + 1 / (n : ℝ))) := by
    have h1 : Filter.Tendsto (fun x => (1 + xsum x n) / Hsum x n) (𝓝[(Set.Ioi 1)] (1 : ℝ))
        (𝓝 ((1 + xsum 1 n) / Hsum 1 n)) :=
      ((hcont 1 (le_refl 1)).continuousWithinAt (s := Set.Ioi 1)).tendsto
    rw [hf1] at h1
    exact h1
  have hnb : Filter.NeBot (𝓝[Set.Ioi 1] (1 : ℝ)) := nhdsWithin_Ioi_neBot (le_refl 1)
  obtain ⟨r₁, hr₁2, hr₁1⟩ := ((htend.eventually_lt_const hk).and self_mem_nhdsWithin).exists
  set R := max (r₁ + 1) k with hR
  have hR1 : 1 ≤ R := by
    rw [hR]
    exact le_max_of_le_left (by linarith)
  have hfR : k < (1 + xsum R n) / Hsum R n := by
    rw [hf_eq R hR1]
    have hpos : 0 < 1 / Hsum R n := one_div_pos.2 (hHpos R hR1)
    have h2 : (k : ℝ) ≤ R := le_max_right _ _
    linarith
  have hcon : ContinuousOn (fun x => (1 + xsum x n) / Hsum x n) (Set.Icc r₁ R) :=
    fun x hx => (hcont x (by linarith [hx.1, hr₁1])).continuousWithinAt
  have hab : r₁ ≤ R := by rw [hR]; linarith [le_max_left (r₁ + 1) (k : ℝ)]
  obtain ⟨r, hrm, hfr⟩ := intermediate_value_Icc hab hcon ⟨le_of_lt hr₁2, le_of_lt hfR⟩
  rw [Set.mem_Icc] at hrm
  exact ⟨r, by linarith [hrm.1, hr₁1], hfr⟩


/-! ### The staircase polygons -/

/-- The vertices of the staircase interface in the big-rectangle coordinates. -/
noncomputable def bfun (r : ℝ) (i : ℕ) : ℂ :=
  if i = 0 then r * I
  else if Even i then -(xsum r (i / 2)) - (ysum r (i / 2 - 1)) * I
  else -(xsum r (i / 2)) - (ysum r (i / 2)) * I

/-- The similarity (ratio `r`) between the two staircase polygons, in the
big-rectangle coordinates. -/
noncomputable def simG (r : ℝ) (z : ℂ) : ℂ := r * I * star z - r ^ 2

/-- The change of coordinates from the staircase rectangle to the standard
rectangle `[0,1] × [0, (1+xsum r n)/Hsum r n]`. -/
noncomputable def simT (r : ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  (I / Hsum r n) * star z + (ysum r (n - 1) + xsum r n * I) / Hsum r n

/-- The inverse of `simT`. -/
noncomputable def simTinv (r : ℝ) (n : ℕ) (w : ℂ) : ℂ :=
  star ((w - (ysum r (n - 1) + xsum r n * I) / Hsum r n) / (I / Hsum r n))

lemma auxI (a b : ℂ) : a * I * (b * I) = -(a * b) := by
  rw [mul_assoc a I (b * I), mul_comm I (b * I), mul_assoc b I I, Complex.I_mul_I]
  ring

/-- The similarity (ratio `r`) between the two polygons in the standard
rectangle, i.e. `simT ∘ simG ∘ simTinv`. -/
noncomputable def simG' (r : ℝ) (n : ℕ) (w : ℂ) : ℂ :=
  r * I * star w + ((I / Hsum r n) * star (-(r ^ 2)) +
    (ysum r (n - 1) + xsum r n * I) / Hsum r n -
    r * I * star ((ysum r (n - 1) + xsum r n * I) / Hsum r n))

lemma bfun_zero (r : ℝ) : bfun r 0 = r * I := by simp [bfun]

lemma bfun_one (r : ℝ) : bfun r 1 = 0 := by simp [bfun]

lemma bfun_even (r : ℝ) {j : ℕ} (hj : 0 < j) :
    bfun r (2 * j) = -(xsum r j) - (ysum r (j - 1)) * I := by
  have h1 : 2 * j ≠ 0 := by omega
  rw [bfun, if_neg h1, if_pos (by rw [Nat.even_iff]; omega),
    show (2 * j) / 2 = j from by omega]

lemma bfun_even_succ (r : ℝ) (j : ℕ) :
    bfun r (2 * (j + 1)) = -(xsum r (j + 1)) - (ysum r j) * I := by
  rw [bfun_even r (by omega : 0 < j + 1), show (j + 1) - 1 = j from by omega]

lemma bfun_odd (r : ℝ) (j : ℕ) :
    bfun r (2 * j + 1) = -(xsum r j) - (ysum r j) * I := by
  have h1 : 2 * j + 1 ≠ 0 := by omega
  have h2 : ¬ Even (2 * j + 1) := by rw [Nat.even_iff]; omega
  rw [bfun, if_neg h1, if_neg h2, show (2 * j + 1) / 2 = j from by omega]

lemma xsum_geom (r : ℝ) (j : ℕ) : xsum r j * (r ^ 2 - 1) = r ^ (2 * j + 2) - r ^ 2 := by
  induction j with
  | zero => simp [xsum_zero]
  | succ j ih =>
    rw [xsum_succ, add_mul, ih]
    ring

lemma r_mul_ysum_add (r : ℝ) (j : ℕ) : r * ysum r j + r ^ 2 = xsum r (j + 1) := by
  rw [ysum_eq_mul_xsum, xsum_succ]
  have h := xsum_geom r j
  ring_nf at h ⊢
  linarith [h]

lemma bfun_edge {r : ℝ} (hr : 1 < r) (i : ℕ) : ‖bfun r (i + 1) - bfun r i‖ = r ^ (i + 1) := by
  rcases Nat.even_or_odd i with (⟨j, rfl⟩ | ⟨j, rfl⟩)
  · rcases j with _ | j
    · rw [bfun_zero, bfun_one, zero_sub, norm_neg, norm_mul, Complex.norm_I, mul_one,
        show ‖((r : ℝ) : ℂ)‖ = |r| from RCLike.norm_ofReal r,
        abs_of_pos (by linarith : (0 : ℝ) < r)]
      ring
    · rw [show (j + 1) + (j + 1) = 2 * (j + 1) from by ring,
        bfun_even_succ r j, bfun_odd r (j + 1)]
      have e : (-(xsum r (j + 1)) - (ysum r (j + 1)) * I) -
          (-(xsum r (j + 1)) - (ysum r j) * I) = (-(r ^ (2 * j + 3) : ℝ)) * I := by
        rw [ysum_succ]
        push_cast
        ring
      rw [e, norm_mul, Complex.norm_I, mul_one, norm_neg,
        show ‖((r ^ (2 * j + 3) : ℝ) : ℂ)‖ = |r ^ (2 * j + 3)| from
          RCLike.norm_ofReal _, abs_of_pos (pow_pos (by linarith) _)]
      ring
  · rw [show 2 * j + 1 + 1 = 2 * (j + 1) from by ring, bfun_odd r j,
      bfun_even_succ r j]
    have e : (-(xsum r (j + 1)) - (ysum r j) * I) - (-(xsum r j) - (ysum r j) * I) =
        -(r ^ (2 * j + 2) : ℝ) := by
      rw [xsum_succ]
      push_cast
      ring
    rw [e, norm_neg, show ‖((r ^ (2 * j + 2) : ℝ) : ℂ)‖ = |r ^ (2 * j + 2)| from
        RCLike.norm_ofReal _, abs_of_pos (pow_pos (by linarith) _)]
    ring

lemma simG_bfun (r : ℝ) (i : ℕ) : simG r (bfun r i) = bfun r (i + 1) := by
  rcases Nat.even_or_odd i with (⟨j, rfl⟩ | ⟨j, rfl⟩)
  · rcases j with _ | j
    · have h0 : (0 : ℕ) + 0 = 0 := rfl
      rw [h0, bfun_zero, bfun_one]
      simp only [simG]
      rw [show star (r * I) = -r * I from by simp, auxI]
      push_cast
      ring
    · have h := r_mul_ysum_add r j
      rw [ysum_eq_mul_xsum] at h
      rw [show (j + 1) + (j + 1) = 2 * (j + 1) from by ring,
        bfun_even_succ r j, bfun_odd r (j + 1)]
      simp only [simG]
      rw [show star (-(xsum r (j + 1)) - (ysum r j) * I) =
          -(xsum r (j + 1)) + (ysum r j) * I from by simp [Complex.conj_I],
        mul_add, mul_neg, auxI, ysum_eq_mul_xsum r j, ysum_eq_mul_xsum r (j + 1), ← h]
      push_cast
      ring
  · have h := r_mul_ysum_add r j
    rw [ysum_eq_mul_xsum] at h
    rw [show 2 * j + 1 + 1 = 2 * (j + 1) from by ring, bfun_odd r j,
      bfun_even_succ r j]
    simp only [simG]
    rw [show star (-(xsum r j) - (ysum r j) * I) =
        -(xsum r j) + (ysum r j) * I from by simp [Complex.conj_I],
      mul_add, mul_neg, auxI, ysum_eq_mul_xsum r j, ← h]
    push_cast
    ring

lemma simG_BR {r : ℝ} (hr : 1 < r) {n : ℕ} (hn : 0 < n) :
    simG r (1 - ysum r (n - 1) * I) = -(xsum r n) + r * I := by
  have h := r_mul_ysum_add r (n - 1)
  rw [show n - 1 + 1 = n from by omega, ysum_eq_mul_xsum] at h
  simp only [simG]
  rw [show star (1 - ysum r (n - 1) * I) = 1 + ysum r (n - 1) * I from by
    simp [Complex.conj_I, sub_neg_eq_add], mul_add, mul_one, auxI,
    ysum_eq_mul_xsum r (n - 1), ← h]
  push_cast
  ring

lemma simG_TR (r : ℝ) : simG r (1 + r * I) = r * I := by
  simp only [simG]
  rw [show star (1 + r * I) = 1 - r * I from by simp [← sub_eq_add_neg],
    mul_sub, mul_one, auxI]
  push_cast
  ring

lemma simT_simG' {r : ℝ} (hr : 1 < r) {n : ℕ} (hn : 0 < n) (z : ℂ) :
    simG' r n (simT r n z) = simT r n (simG r z) := by
  have hH : Hsum r n ≠ 0 := (Hsum_pos (by linarith) hn).ne'
  have e1 : star ((I / Hsum r n) * star z +
        (ysum r (n - 1) + xsum r n * I) / Hsum r n) =
      -(I / Hsum r n) * z + star ((ysum r (n - 1) + xsum r n * I) / Hsum r n) := by
    simp [map_add, map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  have e2 : r * I * (-(I / Hsum r n) * z) = (I / Hsum r n) * (-(r * I) * z) := by
    apply Complex.ext_iff.2
    constructor <;>
      simp [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.I_re,
        Complex.I_im, Complex.div_re, Complex.div_im, Complex.ofReal_re, Complex.ofReal_im] <;>
      ring
  simp only [simG', simT, simG]
  rw [e1, mul_add, e2]
  simp [map_add, map_sub, map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

lemma simT_simTinv {r : ℝ} (hr : 1 < r) {n : ℕ} (hn : 0 < n) (w : ℂ) :
    simT r n (simTinv r n w) = w := by
  have hH : Hsum r n ≠ 0 := (Hsum_pos (by linarith) hn).ne'
  have hH' : ((Hsum r n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hH
  have hiH : (I / Hsum r n) ≠ 0 := div_ne_zero Complex.I_ne_zero hH'
  simp only [simTinv, simT, star_star]
  rw [mul_div_assoc', mul_div_cancel_left₀ _ hiH]
  ring

lemma simT_sub {r : ℝ} (n : ℕ) (z w : ℂ) :
    simT r n z - simT r n w = (I / Hsum r n) * star (z - w) := by
  simp [simT, map_sub]
  ring


/-! ### Assembling the dissection -/

lemma tail_append_singleton {α : Type*} (L : List α) (x : α) (hL : L ≠ []) :
    (L ++ [x]).tail = L.tail ++ [x] := by
  obtain ⟨a, rest, hr⟩ := List.exists_cons_of_ne_nil hL
  rw [hr]
  simp

lemma dropLast_snoc {α : Type*} (L : List α) (x : α) : (L ++ [x]).dropLast = L := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    cases L with
    | nil => rfl
    | cons b L =>
      rw [List.cons_append,
        show (a :: (b :: L ++ [x])).dropLast = a :: ((b :: L ++ [x]).dropLast) from rfl, ih]

lemma map_succ_range (f : ℕ → ℂ) (m : ℕ) :
    (List.range (m + 1)).map (fun i => f (i + 1)) =
      ((List.range (m + 1)).map f).tail ++ [f (m + 1)] := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.map_singleton, ih]
    rw [List.map_append, List.map_singleton,
      tail_append_singleton ((List.range (m + 1)).map f) (f (m + 1)) (by simp)]

lemma isChain_map_range {f : ℕ → ℂ} {R : ℂ → ℂ → Prop} (h : ∀ i, R (f i) (f (i + 1)))
    (m : ℕ) :
    ((List.range (m + 1)).map f).IsChain R := by
  induction m with
  | zero => simp
  | succ m ih =>
    cases m with
    | zero =>
      rw [show List.range 2 = [0, 1] from rfl, List.map_cons, List.map_singleton,
        List.isChain_pair]
      exact h 0
    | succ m =>
      rw [List.range_succ, List.map_append, List.map_singleton, List.range_succ,
        List.map_append, List.map_singleton, List.append_assoc, List.singleton_append,
        List.isChain_append_cons_cons]
      refine ⟨?_, h _, List.isChain_singleton _⟩
      rw [List.range_succ, List.map_append, List.map_singleton] at ih
      exact ih

lemma simT_re {r : ℝ} (hr : 1 < r) {n : ℕ} (hn : 0 < n) (z : ℂ) :
    (simT r n z).re = (z.im + ysum r (n - 1)) / Hsum r n := by
  have hH : Hsum r n ≠ 0 := (Hsum_pos (by linarith) hn).ne'
  simp [simT, Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im,
    Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
    Complex.ofReal_im]
  field_simp [hH]

lemma simT_im {r : ℝ} (hr : 1 < r) {n : ℕ} (hn : 0 < n) (z : ℂ) :
    (simT r n z).im = (z.re + xsum r n) / Hsum r n := by
  have hH : Hsum r n ≠ 0 := (Hsum_pos (by linarith) hn).ne'
  simp [simT, Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im,
    Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
    Complex.ofReal_im]
  field_simp [hH]

lemma simT_norm_sub {r : ℝ} (hr : 1 < r) {n : ℕ} (hn : 0 < n) (z w : ℂ) :
    ‖simT r n z - simT r n w‖ = ‖z - w‖ / Hsum r n := by
  rw [simT_sub, norm_mul, norm_div, Complex.norm_I, norm_star,
    show ‖((Hsum r n : ℝ) : ℂ)‖ = Hsum r n from by
      simp [abs_of_pos (Hsum_pos (by linarith) hn)]]
  ring


lemma ne_nil_of_length_pos {α : Type*} {l : List α} (h : 0 < l.length) : l ≠ [] := by
  intro hnl
  rw [hnl] at h
  simp at h

lemma ratio_facts {r : ℝ} (hr : 1 < r) {n : ℕ} (hn : 0 < n) :
    0 < xsum r n / (1 + xsum r n) ∧ xsum r n / (1 + xsum r n) < 1 ∧
    0 < r ^ (2 * n) / (1 + xsum r n) ∧ r ^ (2 * n) / (1 + xsum r n) < 1 := by
  have hx : 0 < xsum r n := by
    rw [xsum]
    exact Finset.sum_pos (fun i _ => pow_pos (by linarith) _)
      (Finset.nonempty_range_iff.2 (by omega))
  have hW : 0 < 1 + xsum r n := by positivity
  have hpow : r ^ (2 * n) < 1 + xsum r n := by
    have h1 : xsum r n = xsum r (n - 1) + r ^ (2 * n) := by
      have h2 := xsum_succ r (n - 1)
      rw [show n - 1 + 1 = n from by omega, show 2 * (n - 1) + 2 = 2 * n from by omega] at h2
      rw [h2]
    rw [h1]
    have h3 : 0 ≤ xsum r (n - 1) := xsum_nonneg (le_of_lt hr) _
    linarith
  exact ⟨div_pos hx hW, (div_lt_one hW).2 (by linarith [xsum_nonneg (le_of_lt hr) n]),
    div_pos (pow_pos (by linarith) _) hW, (div_lt_one hW).2 hpow⟩

/-- The top boundary arc of the standard rectangle in the staircase construction. -/
noncomputable def arcA (r : ℝ) (n : ℕ) (hr : 1 < r) (hn : 0 < n) :
    BoundaryArc (1 + xsum r n / (1 + xsum r n)) (4 - r ^ (2 * n) / (1 + xsum r n)) where
  s := [1 + xsum r n / (1 + xsum r n), 2, 3, 4 - r ^ (2 * n) / (1 + xsum r n)]
  hne := by simp
  hhead := rfl
  hlast := rfl
  hmono := by
    have ⟨g1, g2, g3, g4⟩ := ratio_facts hr hn
    rw [List.isChain_cons_cons, List.isChain_cons_cons, List.isChain_cons_cons]
    exact ⟨by linarith, by norm_num, by linarith, List.isChain_singleton _⟩
  hside := by
    have ⟨g1, g2, g3, g4⟩ := ratio_facts hr hn
    rw [List.isChain_cons_cons, List.isChain_cons_cons, List.isChain_cons_cons]
    exact ⟨⟨1, by push_cast; linarith, by norm_num⟩,
      ⟨2, by norm_num, by norm_num⟩,
      ⟨3, by norm_num, by push_cast; linarith⟩,
      List.isChain_singleton _⟩
  hint := by
    intro x hx h2 h3
    fin_cases hx <;> simp_all
    · exact ⟨2, by norm_num⟩
    · exact ⟨3, by norm_num⟩
  hcover := by
    intro c h1 h2
    have ⟨g1, g2, g3, g4⟩ := ratio_facts hr hn
    have hc2 : 2 ≤ c := by
      have h4 : (1 : ℝ) < (c : ℝ) := by linarith
      have h5 : (1 : ℤ) < c := by exact_mod_cast h4
      omega
    have hc3 : c ≤ 3 := by
      have h6 : (c : ℝ) < (4 : ℝ) := by linarith
      have h7 : c < (4 : ℤ) := by exact_mod_cast h6
      omega
    interval_cases c <;> simp

/-- The bottom boundary arc of the standard rectangle in the staircase construction. -/
noncomputable def arcC (r : ℝ) (n : ℕ) (hr : 1 < r) (hn : 0 < n) :
    BoundaryArc (4 - r ^ (2 * n) / (1 + xsum r n)) (1 + xsum r n / (1 + xsum r n) + 4) where
  s := [4 - r ^ (2 * n) / (1 + xsum r n), 4, 5, 1 + xsum r n / (1 + xsum r n) + 4]
  hne := by simp
  hhead := rfl
  hlast := rfl
  hmono := by
    have ⟨g1, g2, g3, g4⟩ := ratio_facts hr hn
    rw [List.isChain_cons_cons, List.isChain_cons_cons, List.isChain_cons_cons]
    exact ⟨by linarith, by norm_num, by linarith, List.isChain_singleton _⟩
  hside := by
    have ⟨g1, g2, g3, g4⟩ := ratio_facts hr hn
    rw [List.isChain_cons_cons, List.isChain_cons_cons, List.isChain_cons_cons]
    exact ⟨⟨3, by push_cast; linarith, by norm_num⟩,
      ⟨4, by norm_num, by norm_num⟩,
      ⟨5, by norm_num, by push_cast; linarith⟩,
      List.isChain_singleton _⟩
  hint := by
    intro x hx h2 h3
    fin_cases hx <;> simp_all
    · exact ⟨4, by norm_num⟩
    · exact ⟨5, by norm_num⟩
  hcover := by
    intro c h1 h2
    have ⟨g1, g2, g3, g4⟩ := ratio_facts hr hn
    have hc4 : 4 ≤ c := by
      have h8 : (3 : ℝ) < (c : ℝ) := by linarith
      have h9 : (3 : ℤ) < c := by exact_mod_cast h8
      omega
    have hc5 : c ≤ 5 := by
      have h10 : (c : ℝ) < (6 : ℝ) := by linarith
      have h11 : c < (6 : ℤ) := by exact_mod_cast h10
      omega
    interval_cases c <;> simp


lemma smul_mul_I (s x : ℝ) : s • ((x : ℂ) * I) = ((s * x : ℝ) : ℂ) * I := by
  rw [Complex.real_smul, ← mul_assoc, ← ofReal_mul]

lemma div_ofReal_re (a b : ℝ) : ((a : ℂ) / (b : ℂ)).re = a / b := by
  rw [show ((a : ℂ) / (b : ℂ)) = ((a / b : ℝ) : ℂ) from by norm_cast, Complex.ofReal_re]

lemma div_ofReal_im (a b : ℝ) : ((a : ℂ) / (b : ℂ)).im = 0 := by
  rw [show ((a : ℂ) / (b : ℂ)) = ((a / b : ℝ) : ℂ) from by norm_cast, Complex.ofReal_im]

lemma sqParam_two (k : ℝ) : sqParam k 2 = 1 + k * I := by
  rw [sqParam_eq_on_Icc k (c := 2) (by norm_num) (by norm_num)]
  norm_num [corner]

lemma sqParam_three (k : ℝ) : sqParam k 3 = k * I := by
  rw [sqParam_eq_on_Icc k (c := 3) (by norm_num) (by norm_num)]
  norm_num [corner]

lemma sqParam_four (k : ℝ) : sqParam k 4 = 0 := by
  rw [sqParam_eq_on_Icc k (c := 4) (by norm_num) (by norm_num)]
  have h4 : (4 : ℤ) % 4 = 0 := by norm_num
  have h5 : (4 + 1 : ℤ) % 4 = 1 := by norm_num
  simp [corner, h4, h5]

lemma sqParam_five (k : ℝ) : sqParam k 5 = 1 := by
  rw [sqParam_eq_on_Icc k (c := 5) (by norm_num) (by norm_num)]
  have h5 : (5 : ℤ) % 4 = 1 := by norm_num
  have h6 : (5 + 1 : ℤ) % 4 = 2 := by norm_num
  simp [corner, h5, h6]

lemma sqParam_t0 {r : ℝ} (hr : 1 < r) {n : ℕ} (hn : 0 < n) :
    sqParam ((1 + xsum r n) / Hsum r n) (1 + xsum r n / (1 + xsum r n)) =
      1 + (xsum r n / Hsum r n) * I := by
  have ⟨g1, g2, g3, g4⟩ := ratio_facts hr hn
  have hW0 : (0 : ℝ) < 1 + xsum r n := by have := xsum_nonneg (le_of_lt hr) n; linarith
  have hH0 : (0 : ℝ) < Hsum r n := Hsum_pos (by linarith) hn
  rw [sqParam_eq_on_Icc ((1 + xsum r n) / Hsum r n) (c := 1)
    (show ((1 : ℤ) : ℝ) ≤ 1 + xsum r n / (1 + xsum r n) from by push_cast; linarith)
    (show 1 + xsum r n / (1 + xsum r n) ≤ (1 : ℤ) + 1 from by push_cast; linarith)]
  have hd : corner ((1 + xsum r n) / Hsum r n) (1 + 1) -
      corner ((1 + xsum r n) / Hsum r n) 1 = ((1 + xsum r n) / Hsum r n) * I := by
    simp [corner_at_one, corner_at_two]
  have hW0' : (1 + ↑(xsum r n) : ℂ) ≠ 0 := by exact_mod_cast hW0.ne'
  have hH0' : (↑(Hsum r n) : ℂ) ≠ 0 := by exact_mod_cast hH0.ne'
  rw [hd, show (1 + xsum r n / (1 + xsum r n) - ((1 : ℤ) : ℝ)) =
      xsum r n / (1 + xsum r n) from by push_cast; ring]
  have key : (xsum r n / (1 + xsum r n) : ℝ) •
      (((1 + ↑(xsum r n)) / ↑(Hsum r n)) * I) = (↑(xsum r n) / ↑(Hsum r n)) * I := by
    rw [Complex.real_smul, ← mul_assoc]
    congr 1
    push_cast
    field_simp [hW0', hH0']
  rw [key, corner_at_one]

lemma sqParam_t1 {r : ℝ} (hr : 1 < r) {n : ℕ} (hn : 0 < n) :
    sqParam ((1 + xsum r n) / Hsum r n) (4 - r ^ (2 * n) / (1 + xsum r n)) =
      (r ^ (2 * n) / Hsum r n) * I := by
  have ⟨g1, g2, g3, g4⟩ := ratio_facts hr hn
  have hW0 : (0 : ℝ) < 1 + xsum r n := by have := xsum_nonneg (le_of_lt hr) n; linarith
  have hH0 : (0 : ℝ) < Hsum r n := Hsum_pos (by linarith) hn
  rw [sqParam_eq_on_Icc ((1 + xsum r n) / Hsum r n) (c := 3)
    (show ((3 : ℤ) : ℝ) ≤ 4 - r ^ (2 * n) / (1 + xsum r n) from by push_cast; linarith)
    (show 4 - r ^ (2 * n) / (1 + xsum r n) ≤ (3 : ℤ) + 1 from by push_cast; linarith)]
  have hd : corner ((1 + xsum r n) / Hsum r n) (3 + 1) -
      corner ((1 + xsum r n) / Hsum r n) 3 = -(((1 + xsum r n) / Hsum r n) * I) := by
    have h4 : corner ((1 + xsum r n) / Hsum r n) (3 + 1) = 0 := by
      have h : (3 + 1 : ℤ) % 4 = 0 := by norm_num
      simp [corner, h]
    rw [h4, corner_at_three]
    push_cast
    ring
  have e : (4 - r ^ (2 * n) / (1 + xsum r n)) - ((3 : ℤ) : ℝ) =
      1 - r ^ (2 * n) / (1 + xsum r n) := by
    push_cast
    ring
  have hW0' : (1 + ↑(xsum r n) : ℂ) ≠ 0 := by exact_mod_cast hW0.ne'
  have hH0' : (↑(Hsum r n) : ℂ) ≠ 0 := by exact_mod_cast hH0.ne'
  rw [hd, e, smul_neg]
  have key : (1 - r ^ (2 * n) / (1 + xsum r n) : ℝ) •
      (((1 + ↑(xsum r n)) / ↑(Hsum r n)) * I) =
      ((1 + ↑(xsum r n) - ↑(r ^ (2 * n))) / ↑(Hsum r n)) * I := by
    rw [Complex.real_smul, ← mul_assoc]
    congr 1
    push_cast
    field_simp [hW0', hH0']
  rw [key, corner_at_three]
  push_cast
  ring

lemma B_head {r : ℝ} (hr : 1 < r) {n : ℕ} (hn : 0 < n) :
    (((List.range (2 * n)).map (bfun r)).map (simT r n)).head! =
      1 + (xsum r n / Hsum r n) * I := by
  have hH : Hsum r n ≠ 0 := (Hsum_pos (by linarith) hn).ne'
  have hne1 : (List.range (2 * n)).map (bfun r) ≠ [] :=
    ne_nil_of_length_pos (by simp; omega)
  have hne2 : ((List.range (2 * n)).map (bfun r)).map (simT r n) ≠ [] :=
    ne_nil_of_length_pos (by simp; omega)
  have hne3 : (List.range (2 * n)) ≠ [] := ne_nil_of_length_pos (by simp; omega)
  rw [head!_map (simT r n) hne1, head!_map (bfun r) hne3,
    show (List.range (2 * n)).head! = 0 from by
      rw [show 2 * n = (2 * n - 1) + 1 from by omega, List.range_succ_eq_map]
      rfl,
    bfun_zero]
  apply Complex.ext_iff.2
  constructor
  · rw [simT_re hr hn]
    simp [Complex.mul_im, Complex.I_im, Complex.ofReal_im]
    have hH' : r + ysum r (n - 1) ≠ 0 := by rwa [Hsum_eq_add_ysum r hn] at hH
    rw [Hsum_eq_add_ysum r hn]
    exact div_self hH'
  · rw [simT_im hr hn]
    simp [Complex.mul_re, Complex.I_re, Complex.ofReal_re]

lemma B_getLast {r : ℝ} (hr : 1 < r) {n : ℕ} (hn : 0 < n) :
    (((List.range (2 * n)).map (bfun r)).map (simT r n)).getLast! =
      (r ^ (2 * n) / Hsum r n) * I := by
  have hne1 : (List.range (2 * n)).map (bfun r) ≠ [] :=
    ne_nil_of_length_pos (by simp; omega)
  have hne2 : ((List.range (2 * n)).map (bfun r)).map (simT r n) ≠ [] :=
    ne_nil_of_length_pos (by simp; omega)
  have hne3 : (List.range (2 * n)) ≠ [] := ne_nil_of_length_pos (by simp; omega)
  rw [getLast!_map (simT r n) hne1, getLast!_map (bfun r) hne3,
    show (List.range (2 * n)).getLast! = 2 * (n - 1) + 1 from by
      rw [show 2 * n = (2 * n - 1) + 1 from by omega, List.range_succ, getLast!_snoc]
      omega,
    bfun_odd r (n - 1)]
  apply Complex.ext_iff.2
  constructor
  · rw [simT_re hr hn]
    have e : (-(xsum r (n - 1)) - (ysum r (n - 1)) * I).im = -(ysum r (n - 1)) := by
      simp [Complex.neg_im, Complex.sub_im, Complex.mul_im, Complex.I_im, Complex.ofReal_im,
        Complex.ofReal_re]
    have hre : (↑r ^ (2 * n) / ↑(Hsum r n) * I).re = 0 := by
      simp [Complex.mul_re, Complex.I_re, Complex.div_im, Complex.I_im, Complex.ofReal_im,
        ← ofReal_pow]
    rw [e, show -(ysum r (n - 1)) + ysum r (n - 1) = (0 : ℝ) from by ring, zero_div, hre]
  · rw [simT_im hr hn]
    have e : (-(xsum r (n - 1)) - (ysum r (n - 1)) * I).re = -(xsum r (n - 1)) := by
      simp [Complex.neg_re, Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.ofReal_re,
        Complex.ofReal_im]
    have him : (↑r ^ (2 * n) / ↑(Hsum r n) * I).im = r ^ (2 * n) / Hsum r n := by
      simp [Complex.mul_im, Complex.I_re, Complex.I_im, div_ofReal_re, ← ofReal_pow]
    rw [e, him]
    have h1 : xsum r n = xsum r (n - 1) + r ^ (2 * n) := by
      have h2 := xsum_succ r (n - 1)
      rw [show n - 1 + 1 = n from by omega, show 2 * (n - 1) + 2 = 2 * n from by omega] at h2
      rw [h2]
    rw [h1, show -(xsum r (n - 1)) + (xsum r (n - 1) + r ^ (2 * n)) = r ^ (2 * n) from by ring]

/-- The interior vertices of the staircase interface map to the interior of the
standard rectangle. -/
lemma bfun_interior {r : ℝ} (hr : 1 < r) {n : ℕ} (hn : 0 < n) {i : ℕ}
    (hi0 : 0 < i) (hi : i < 2 * n - 1) :
    0 < (simT r n (bfun r i)).re ∧ (simT r n (bfun r i)).re < 1 ∧
      0 < (simT r n (bfun r i)).im ∧
      (simT r n (bfun r i)).im < (1 + xsum r n) / Hsum r n := by
  have hH : 0 < Hsum r n := Hsum_pos (by linarith) hn
  have hHe : Hsum r n = r + ysum r (n - 1) := Hsum_eq_add_ysum r hn
  rcases Nat.even_or_odd i with (⟨j, rfl⟩ | ⟨j, rfl⟩)
  · have hj0 : 0 < j := by omega
    have hjn : j < n := by omega
    rw [show j + j = 2 * j from by ring, bfun_even r hj0]
    have hy1 : ysum r (j - 1) < ysum r (n - 1) := ysum_strictMono hr (by omega)
    have hy0 : 0 ≤ ysum r (j - 1) := ysum_nonneg (le_of_lt hr) _
    have hx1 : xsum r j < xsum r n := xsum_strictMono hr hjn
    have hx0 : 0 ≤ xsum r j := xsum_nonneg (le_of_lt hr) _
    have him : (-(xsum r j) - (ysum r (j - 1)) * I).im = -(ysum r (j - 1)) := by
      simp [Complex.neg_im, Complex.sub_im, Complex.mul_im, Complex.I_im, Complex.ofReal_im,
        Complex.ofReal_re]
    have hre : (-(xsum r j) - (ysum r (j - 1)) * I).re = -(xsum r j) := by
      simp [Complex.neg_re, Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.ofReal_re,
        Complex.ofReal_im]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [simT_re hr hn, him]
      exact div_pos (by linarith) hH
    · rw [simT_re hr hn, him, div_lt_one hH]
      linarith
    · rw [simT_im hr hn, hre]
      exact div_pos (by linarith) hH
    · rw [simT_im hr hn, hre, div_lt_div_iff_of_pos_right hH]
      linarith
  · have hjn : j < n - 1 := by omega
    rw [bfun_odd r j]
    have hy1 : ysum r j < ysum r (n - 1) := ysum_strictMono hr (by omega)
    have hy0 : 0 ≤ ysum r j := ysum_nonneg (le_of_lt hr) _
    have hx1 : xsum r j < xsum r n := xsum_strictMono hr (by omega)
    have hx0 : 0 ≤ xsum r j := xsum_nonneg (le_of_lt hr) _
    have him : (-(xsum r j) - (ysum r j) * I).im = -(ysum r j) := by
      simp [Complex.neg_im, Complex.sub_im, Complex.mul_im, Complex.I_im, Complex.ofReal_im,
        Complex.ofReal_re]
    have hre : (-(xsum r j) - (ysum r j) * I).re = -(xsum r j) := by
      simp [Complex.neg_re, Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.ofReal_re,
        Complex.ofReal_im]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [simT_re hr hn, him]
      exact div_pos (by linarith) hH
    · rw [simT_re hr hn, him, div_lt_one hH]
      linarith
    · rw [simT_im hr hn, hre]
      exact div_pos (by linarith) hH
    · rw [simT_im hr hn, hre, div_lt_div_iff_of_pos_right hH]
      linarith

/-- The interior vertices of the staircase interface, as a list. -/
lemma range_tail_dropLast {n : ℕ} (hn : 0 < n) :
    (List.range (2 * n)).tail.dropLast = (List.range (2 * n - 2)).map (· + 1) := by
  conv_lhs => rw [show 2 * n = (2 * n - 1) + 1 from by omega, List.range_succ_eq_map,
    List.tail_cons, ← List.map_dropLast, show 2 * n - 1 = (2 * n - 2) + 1 from by omega,
    List.range_succ, dropLast_snoc]

/-- The interior vertices of the staircase interface, as a list. -/
lemma B_tail_dropLast (r : ℝ) {n : ℕ} (hn : 0 < n) :
    (((List.range (2 * n)).map (bfun r)).map (simT r n)).tail.dropLast =
      ((List.range (2 * n - 2)).map fun j => simT r n (bfun r (j + 1))) := by
  rw [← List.map_tail, ← List.map_dropLast, ← List.map_tail, ← List.map_dropLast, List.map_map,
    range_tail_dropLast hn, List.map_map]
  apply List.map_congr_left
  intro j hj
  simp [Function.comp_apply]

/-- Every interior vertex of the staircase interface lies in the interior of the
standard rectangle. -/
lemma B_interior {r : ℝ} (hr : 1 < r) {n : ℕ} (hn : 0 < n) :
    ∀ z ∈ (((List.range (2 * n)).map (bfun r)).map (simT r n)).tail.dropLast,
      0 < z.re ∧ z.re < 1 ∧ 0 < z.im ∧ z.im < (1 + xsum r n) / Hsum r n := by
  intro z hz
  rw [B_tail_dropLast r hn, List.mem_map] at hz
  obtain ⟨j, hj, rfl⟩ := hz
  rw [List.mem_range] at hj
  exact bfun_interior hr hn (by omega : 0 < j + 1) (by omega : j + 1 < 2 * n - 1)

/-- The staircase interface has no repeated consecutive vertices. -/
lemma B_chain {r : ℝ} (hr : 1 < r) {n : ℕ} (hn : 0 < n) :
    (((List.range (2 * n)).map (bfun r)).map (simT r n)).IsChain (· ≠ ·) := by
  rw [List.map_map, show 2 * n = (2 * n - 1) + 1 from by omega]
  apply isChain_map_range
  intro i hcon
  simp only [Function.comp_apply] at hcon
  have hH : 0 < Hsum r n := Hsum_pos (by linarith) hn
  have h1 := simT_norm_sub hr hn (bfun r i) (bfun r (i + 1))
  rw [hcon, sub_self, norm_zero] at h1
  have h3 : ‖bfun r i - bfun r (i + 1)‖ = 0 := by
    rcases div_eq_zero_iff.1 h1.symm with h | h
    · exact h
    · linarith
  rw [norm_sub_rev, bfun_edge hr] at h3
  exact (pow_pos (by linarith) _).ne' h3

/-- The edge lengths of the staircase interface. -/
lemma chainEdges_B {r : ℝ} (hr : 1 < r) {n : ℕ} (hn : 0 < n) :
    chainEdges (((List.range (2 * n)).map (bfun r)).map (simT r n)) =
      (List.range (2 * n - 1)).map fun i => r ^ (i + 1) / Hsum r n := by
  rw [List.map_map, show 2 * n = (2 * n - 1) + 1 from by omega, chainEdges_map_range]
  apply List.map_congr_left
  intro i hi
  rw [Function.comp_apply, Function.comp_apply, simT_norm_sub hr hn, bfun_edge hr]

/-- The image of the big-rectangle corner `(1, -ysum)` under `simT`. -/
lemma simT_qI {r : ℝ} (hr : 1 < r) {n : ℕ} (hn : 0 < n) :
    simT r n (1 - (ysum r (n - 1)) * I) =
      (((1 + xsum r n) / Hsum r n : ℝ) : ℂ) * I := by
  have him : (1 - (ysum r (n - 1)) * I).im = -(ysum r (n - 1)) := by
    simp [Complex.sub_im, Complex.one_im, Complex.mul_im, Complex.I_im, Complex.ofReal_im,
      Complex.ofReal_re]
  have hre : (1 - (ysum r (n - 1)) * I).re = 1 := by
    simp [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.I_re, Complex.ofReal_re,
      Complex.ofReal_im]
  apply Complex.ext_iff.2
  constructor
  · rw [simT_re hr hn, him, show -(ysum r (n - 1)) + ysum r (n - 1) = (0 : ℝ) from by ring,
      zero_div]
    simp [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  · rw [simT_im hr hn, hre]
    simp [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]

/-- The image of the big-rectangle corner `(1, r)` under `simT`. -/
lemma simT_one_add_qI {r : ℝ} (hr : 1 < r) {n : ℕ} (hn : 0 < n) :
    simT r n (1 + r * I) = 1 + (((1 + xsum r n) / Hsum r n : ℝ) : ℂ) * I := by
  have hH : Hsum r n ≠ 0 := (Hsum_pos (by linarith) hn).ne'
  have him : (1 + r * I).im = r := by
    simp [Complex.add_im, Complex.one_im, Complex.mul_im, Complex.I_im, Complex.ofReal_im]
  have hre : (1 + r * I).re = 1 := by
    simp [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.I_re, Complex.ofReal_re,
      Complex.ofReal_im]
  apply Complex.ext_iff.2
  constructor
  · rw [simT_re hr hn, him]
    have hRhs : (1 + (((1 + xsum r n) / Hsum r n : ℝ) : ℂ) * I).re = 1 := by
      simp [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.I_re, Complex.ofReal_re,
        Complex.ofReal_im]
    have hH' : r + ysum r (n - 1) ≠ 0 := by rwa [Hsum_eq_add_ysum r hn] at hH
    rw [hRhs, Hsum_eq_add_ysum r hn, div_self hH']
  · rw [simT_im hr hn, hre]
    simp [Complex.add_im, Complex.one_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]

/-- The image of the big-rectangle corner `(-xsum, -ysum)` under `simT`. -/
lemma simT_zero {r : ℝ} (hr : 1 < r) {n : ℕ} (hn : 0 < n) :
    simT r n (-(xsum r n) - (ysum r (n - 1)) * I) = 0 := by
  have him : (-(xsum r n) - (ysum r (n - 1)) * I).im = -(ysum r (n - 1)) := by
    simp [Complex.neg_im, Complex.sub_im, Complex.mul_im, Complex.I_im, Complex.ofReal_im,
      Complex.ofReal_re]
  have hre : (-(xsum r n) - (ysum r (n - 1)) * I).re = -(xsum r n) := by
    simp [Complex.neg_re, Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.ofReal_re,
      Complex.ofReal_im]
  apply Complex.ext_iff.2
  constructor
  · rw [simT_re hr hn, him, show -(ysum r (n - 1)) + ysum r (n - 1) = (0 : ℝ) from by ring,
      zero_div, Complex.zero_re]
  · rw [simT_im hr hn, hre, show -(xsum r n) + xsum r n = (0 : ℝ) from by ring, zero_div,
      Complex.zero_im]

/-- The image of the big-rectangle corner `(-xsum, r)` under `simT`. -/
lemma simT_one {r : ℝ} (hr : 1 < r) {n : ℕ} (hn : 0 < n) :
    simT r n (-(xsum r n) + r * I) = 1 := by
  have hH : Hsum r n ≠ 0 := (Hsum_pos (by linarith) hn).ne'
  have him : (-(xsum r n) + r * I).im = r := by
    simp [Complex.neg_im, Complex.add_im, Complex.mul_im, Complex.I_im, Complex.ofReal_im,
      Complex.ofReal_re]
  have hre : (-(xsum r n) + r * I).re = -(xsum r n) := by
    simp [Complex.neg_re, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.ofReal_re,
      Complex.ofReal_im]
  apply Complex.ext_iff.2
  constructor
  · rw [simT_re hr hn, him]
    have hH' : r + ysum r (n - 1) ≠ 0 := by rwa [Hsum_eq_add_ysum r hn] at hH
    rw [Hsum_eq_add_ysum r hn, div_self hH', Complex.one_re]
  · rw [simT_im hr hn, hre, show -(xsum r n) + xsum r n = (0 : ℝ) from by ring, zero_div,
      Complex.one_im]

/-- The vertices contributed by the top arc to the top polygon. -/
lemma arcA_reverse_tail_dropLast {r : ℝ} (hr : 1 < r) {n : ℕ} (hn : 0 < n) :
    ((arcA r n hr hn).points ((1 + xsum r n) / Hsum r n)).reverse.tail.dropLast =
      [(((1 + xsum r n) / Hsum r n : ℝ) : ℂ) * I,
        1 + (((1 + xsum r n) / Hsum r n : ℝ) : ℂ) * I] := by
  have h1 : (arcA r n hr hn).points ((1 + xsum r n) / Hsum r n) =
      [sqParam ((1 + xsum r n) / Hsum r n) (1 + xsum r n / (1 + xsum r n)),
        sqParam ((1 + xsum r n) / Hsum r n) 2,
        sqParam ((1 + xsum r n) / Hsum r n) 3,
        sqParam ((1 + xsum r n) / Hsum r n) (4 - r ^ (2 * n) / (1 + xsum r n))] := rfl
  rw [h1]
  show [sqParam ((1 + xsum r n) / Hsum r n) 3, sqParam ((1 + xsum r n) / Hsum r n) 2] = _
  rw [sqParam_three, sqParam_two]

/-- The vertices contributed by the bottom arc to the bottom polygon. -/
lemma arcC_tail_dropLast {r : ℝ} (hr : 1 < r) {n : ℕ} (hn : 0 < n) :
    ((arcC r n hr hn).points ((1 + xsum r n) / Hsum r n)).tail.dropLast = [0, 1] := by
  have h1 : (arcC r n hr hn).points ((1 + xsum r n) / Hsum r n) =
      [sqParam ((1 + xsum r n) / Hsum r n) (4 - r ^ (2 * n) / (1 + xsum r n)),
        sqParam ((1 + xsum r n) / Hsum r n) 4,
        sqParam ((1 + xsum r n) / Hsum r n) 5,
        sqParam ((1 + xsum r n) / Hsum r n) (1 + xsum r n / (1 + xsum r n) + 4)] := rfl
  rw [h1]
  show [sqParam ((1 + xsum r n) / Hsum r n) 4, sqParam ((1 + xsum r n) / Hsum r n) 5] = [0, 1]
  rw [sqParam_four, sqParam_five]

/-- Mapping the staircase vertices by the similarity shifts them by one. -/
lemma map_simG_bfun (r : ℝ) (m : ℕ) :
    ((List.range m).map (bfun r)).map (simG r) = (List.range m).map fun i => bfun r (i + 1) := by
  rw [List.map_map]
  apply List.map_congr_left
  intro a ha
  rw [Function.comp_apply]
  exact simG_bfun r a

/-- The similarity between the two staircase polygons, in the big-rectangle
coordinates: the image of the small polygon is a cyclic shift of the big one. -/
lemma stair_sim {r : ℝ} (hr : 1 < r) {n : ℕ} (hn : 0 < n) :
    (((List.range (2 * n)).map (bfun r)) ++ [1 - (ysum r (n - 1)) * I, 1 + r * I]).map
        (simG r) =
      (((List.range (2 * n)).map (bfun r)) ++
        [-(xsum r n) - (ysum r (n - 1)) * I, -(xsum r n) + r * I]).rotate 1 := by
  have h1 : (List.range (2 * n)).map (bfun r) =
      bfun r 0 :: ((List.range (2 * n)).map (bfun r)).tail := by
    rw [show 2 * n = (2 * n - 1) + 1 from by omega, List.range_succ_eq_map]
    rfl
  have h2 : (List.range (2 * n)).map (fun i => bfun r (i + 1)) =
      ((List.range (2 * n)).map (bfun r)).tail ++ [bfun r (2 * n)] := by
    conv_lhs => rw [show 2 * n = (2 * n - 1) + 1 from by omega]
    rw [map_succ_range (bfun r) (2 * n - 1), show 2 * n - 1 + 1 = 2 * n from by omega]
  have rot1 : ∀ (a : ℂ) (l : List ℂ), (a :: l).rotate 1 = l ++ [a] := fun a l => by
    rw [show (1 : ℕ) = 0 + 1 from rfl, List.rotate_cons_succ, List.rotate_zero]
  conv_rhs => rw [h1, List.cons_append, rot1, List.append_assoc]
  rw [List.map_append, map_simG_bfun, h2,
    show ([1 - (ysum r (n - 1)) * I, 1 + r * I]).map (simG r) =
      [simG r (1 - (ysum r (n - 1)) * I), simG r (1 + r * I)] from rfl,
    simG_BR hr hn, simG_TR, bfun_even r hn]
  conv_lhs => rw [List.append_assoc, ← bfun_zero]
  rfl

/-- The top polygon is the image of the big-coordinates small polygon. -/
lemma P_std_eq {r : ℝ} (hr : 1 < r) {n : ℕ} (hn : 0 < n) :
    (((List.range (2 * n)).map (bfun r)).map (simT r n)) ++
        [(((1 + xsum r n) / Hsum r n : ℝ) : ℂ) * I,
          1 + (((1 + xsum r n) / Hsum r n : ℝ) : ℂ) * I] =
      (((List.range (2 * n)).map (bfun r)) ++ [1 - (ysum r (n - 1)) * I, 1 + r * I]).map
        (simT r n) := by
  rw [List.map_append]
  congr 1
  rw [show ([1 - (ysum r (n - 1)) * I, 1 + r * I]).map (simT r n) =
      [simT r n (1 - (ysum r (n - 1)) * I), simT r n (1 + r * I)] from rfl,
    simT_qI hr hn, simT_one_add_qI hr hn]

/-- The bottom polygon is the image of the big-coordinates big polygon. -/
lemma Q_std_eq {r : ℝ} (hr : 1 < r) {n : ℕ} (hn : 0 < n) :
    (((List.range (2 * n)).map (bfun r)).map (simT r n)) ++ [0, 1] =
      (((List.range (2 * n)).map (bfun r)) ++
        [-(xsum r n) - (ysum r (n - 1)) * I, -(xsum r n) + r * I]).map (simT r n) := by
  rw [List.map_append]
  congr 1
  rw [show ([-(xsum r n) - (ysum r (n - 1)) * I, -(xsum r n) + r * I]).map (simT r n) =
      [simT r n (-(xsum r n) - (ysum r (n - 1)) * I), simT r n (-(xsum r n) + r * I)]
      from rfl,
    simT_zero hr hn, simT_one hr hn]

/-- The two staircase polygons are similar. -/
lemma PQ_similar {r : ℝ} (hr : 1 < r) {n : ℕ} (hn : 0 < n) :
    CycleSimilar
      ((((List.range (2 * n)).map (bfun r)).map (simT r n)) ++
        [(((1 + xsum r n) / Hsum r n : ℝ) : ℂ) * I,
          1 + (((1 + xsum r n) / Hsum r n : ℝ) : ℂ) * I])
      ((((List.range (2 * n)).map (bfun r)).map (simT r n)) ++ [0, 1]) := by
  set P := (((List.range (2 * n)).map (bfun r)).map (simT r n)) ++
    [(((1 + xsum r n) / Hsum r n : ℝ) : ℂ) * I,
      1 + (((1 + xsum r n) / Hsum r n : ℝ) : ℂ) * I]
  set Q := (((List.range (2 * n)).map (bfun r)).map (simT r n)) ++ [0, 1]
  have hPe : P = (((List.range (2 * n)).map (bfun r)) ++
      [1 - (ysum r (n - 1)) * I, 1 + r * I]).map (simT r n) := P_std_eq hr hn
  have hQe : Q = (((List.range (2 * n)).map (bfun r)) ++
      [-(xsum r n) - (ysum r (n - 1)) * I, -(xsum r n) + r * I]).map (simT r n) :=
    Q_std_eq hr hn
  have hL : Q.length = 2 * n + 2 := by simp [Q]
  have hsim1 : P.map (simG' r n) = Q.rotate 1 := by
    rw [hPe, hQe]
    have hcomp : ((((List.range (2 * n)).map (bfun r)) ++
          [1 - (ysum r (n - 1)) * I, 1 + r * I]).map (simT r n)).map (simG' r n) =
        ((((List.range (2 * n)).map (bfun r)) ++
          [1 - (ysum r (n - 1)) * I, 1 + r * I]).map (simG r)).map (simT r n) := by
      rw [List.map_map, List.map_map]
      apply List.map_congr_left
      intro a ha
      rw [Function.comp_apply, Function.comp_apply]
      exact simT_simG' hr hn a
    rw [hcomp, stair_sim hr hn, List.map_rotate]
  have hα : (r : ℂ) * I ≠ 0 :=
    mul_ne_zero (by exact_mod_cast (by linarith : (0 : ℝ) < r).ne') Complex.I_ne_zero
  refine CycleSimilar.of_conj (β := ((I / Hsum r n) * star (-(r ^ 2)) +
      (ysum r (n - 1) + xsum r n * I) / Hsum r n -
      r * I * star ((ysum r (n - 1) + xsum r n * I) / Hsum r n))) hα (m := 2 * n + 1) ?_
  show Q = (P.map (simG' r n)).rotate (2 * n + 1)
  rw [hsim1, List.rotate_rotate, show 1 + (2 * n + 1) = 2 * n + 2 from by ring, ← hL,
    List.rotate_length]

/-- The norm of a real number as a complex number. -/
lemma norm_ofReal' (x : ℝ) : ‖((x : ℝ) : ℂ)‖ = |x| := RCLike.norm_ofReal _

/-- The norm of a difference of pure-imaginary real multiples. -/
lemma norm_sub_mul_I (a b : ℝ) : ‖((a : ℝ) : ℂ) * I - ((b : ℝ) : ℂ) * I‖ = |a - b| := by
  have h1 : ((a : ℝ) : ℂ) * I - ((b : ℝ) : ℂ) * I = ((a - b : ℝ) : ℂ) * I := by
    push_cast
    ring
  rw [h1, norm_mul, Complex.norm_I, mul_one, norm_ofReal']

/-- The edges along the (reversed) top arc. -/
lemma chainEdges_arcA_reverse {r : ℝ} (hr : 1 < r) {n : ℕ} (hn : 0 < n) :
    chainEdges (((arcA r n hr hn).points ((1 + xsum r n) / Hsum r n)).reverse) =
      [(1 + xsum r (n - 1)) / Hsum r n, 1, 1 / Hsum r n] := by
  have hH : 0 < Hsum r n := Hsum_pos (by linarith) hn
  have h2 := xsum_succ r (n - 1)
  rw [show n - 1 + 1 = n from by omega, show 2 * (n - 1) + 2 = 2 * n from by omega] at h2
  have h1 : ((arcA r n hr hn).points ((1 + xsum r n) / Hsum r n)).reverse =
      [sqParam ((1 + xsum r n) / Hsum r n) (4 - r ^ (2 * n) / (1 + xsum r n)),
        sqParam ((1 + xsum r n) / Hsum r n) 3,
        sqParam ((1 + xsum r n) / Hsum r n) 2,
        sqParam ((1 + xsum r n) / Hsum r n) (1 + xsum r n / (1 + xsum r n))] := rfl
  have sq1 : sqParam ((1 + xsum r n) / Hsum r n) (4 - r ^ (2 * n) / (1 + xsum r n)) =
      (((r ^ (2 * n)) / Hsum r n : ℝ) : ℂ) * I := by
    rw [sqParam_t1 hr hn]
    norm_cast
  have sq3 : sqParam ((1 + xsum r n) / Hsum r n) 3 =
      (((1 + xsum r n) / Hsum r n : ℝ) : ℂ) * I := sqParam_three _
  have sq2 : sqParam ((1 + xsum r n) / Hsum r n) 2 =
      1 + (((1 + xsum r n) / Hsum r n : ℝ) : ℂ) * I := sqParam_two _
  have sq0 : sqParam ((1 + xsum r n) / Hsum r n) (1 + xsum r n / (1 + xsum r n)) =
      1 + (((xsum r n) / Hsum r n : ℝ) : ℂ) * I := by
    rw [sqParam_t0 hr hn]
    norm_cast
  have ce : ∀ (a b c d : ℂ), chainEdges [a, b, c, d] = [‖a - b‖, ‖b - c‖, ‖c - d‖] :=
    fun a b c d => rfl
  rw [h1, sq1, sq3, sq2, sq0, ce]
  have hpos1 : 0 < (1 + xsum r n) / Hsum r n - r ^ (2 * n) / Hsum r n := by
    rw [div_sub_div_same]
    exact div_pos (by linarith [xsum_nonneg (le_of_lt hr) (n - 1)] :
      (0 : ℝ) < 1 + xsum r n - r ^ (2 * n)) hH
  have e1 : ‖(((r ^ (2 * n)) / Hsum r n : ℝ) : ℂ) * I -
      (((1 + xsum r n) / Hsum r n : ℝ) : ℂ) * I‖ = (1 + xsum r (n - 1)) / Hsum r n := by
    rw [norm_sub_mul_I, abs_sub_comm, abs_of_pos hpos1, div_sub_div_same]
    congr 1
    rw [h2]
    ring
  have e2 : ‖(((1 + xsum r n) / Hsum r n : ℝ) : ℂ) * I -
      (1 + (((1 + xsum r n) / Hsum r n : ℝ) : ℂ) * I)‖ = 1 := by
    rw [show (((1 + xsum r n) / Hsum r n : ℝ) : ℂ) * I -
        (1 + (((1 + xsum r n) / Hsum r n : ℝ) : ℂ) * I) = -1 from by ring, norm_neg,
      norm_one]
  have hpos3 : 0 < (1 + xsum r n) / Hsum r n - (xsum r n) / Hsum r n := by
    rw [div_sub_div_same]
    exact div_pos (by linarith [xsum_nonneg (le_of_lt hr) n] :
      (0 : ℝ) < 1 + xsum r n - xsum r n) hH
  have e3 : ‖1 + (((1 + xsum r n) / Hsum r n : ℝ) : ℂ) * I -
      (1 + (((xsum r n) / Hsum r n : ℝ) : ℂ) * I)‖ = 1 / Hsum r n := by
    rw [show 1 + (((1 + xsum r n) / Hsum r n : ℝ) : ℂ) * I -
        (1 + (((xsum r n) / Hsum r n : ℝ) : ℂ) * I) =
        (((1 + xsum r n) / Hsum r n : ℝ) : ℂ) * I - (((xsum r n) / Hsum r n : ℝ) : ℂ) * I
        from by ring]
    rw [norm_sub_mul_I, abs_of_pos hpos3, div_sub_div_same]
    congr 1
    ring
  rw [e1, e2, e3]

/-- The edges along the bottom arc. -/
lemma chainEdges_arcC {r : ℝ} (hr : 1 < r) {n : ℕ} (hn : 0 < n) :
    chainEdges ((arcC r n hr hn).points ((1 + xsum r n) / Hsum r n)) =
      [r ^ (2 * n) / Hsum r n, 1, xsum r n / Hsum r n] := by
  have hH : 0 < Hsum r n := Hsum_pos (by linarith) hn
  have hxpos : 0 < xsum r n := by
    rw [xsum]
    exact Finset.sum_pos (fun i _ => pow_pos (by linarith) _)
      (Finset.nonempty_range_iff.2 (by omega))
  have h1 : (arcC r n hr hn).points ((1 + xsum r n) / Hsum r n) =
      [sqParam ((1 + xsum r n) / Hsum r n) (4 - r ^ (2 * n) / (1 + xsum r n)),
        sqParam ((1 + xsum r n) / Hsum r n) 4,
        sqParam ((1 + xsum r n) / Hsum r n) 5,
        sqParam ((1 + xsum r n) / Hsum r n) (1 + xsum r n / (1 + xsum r n) + 4)] := rfl
  have sq1 : sqParam ((1 + xsum r n) / Hsum r n) (4 - r ^ (2 * n) / (1 + xsum r n)) =
      (((r ^ (2 * n)) / Hsum r n : ℝ) : ℂ) * I := by
    rw [sqParam_t1 hr hn]
    norm_cast
  have sq0 : sqParam ((1 + xsum r n) / Hsum r n) (1 + xsum r n / (1 + xsum r n) + 4) =
      1 + (((xsum r n) / Hsum r n : ℝ) : ℂ) * I := by
    rw [sqParam_periodic, sqParam_t0 hr hn]
    norm_cast
  have ce : ∀ (a b c d : ℂ), chainEdges [a, b, c, d] = [‖a - b‖, ‖b - c‖, ‖c - d‖] :=
    fun a b c d => rfl
  rw [h1, sq1, sqParam_four, sqParam_five, sq0, ce]
  have e1 : ‖(((r ^ (2 * n)) / Hsum r n : ℝ) : ℂ) * I - 0‖ = r ^ (2 * n) / Hsum r n := by
    rw [sub_zero, norm_mul, Complex.norm_I, mul_one, norm_ofReal',
      abs_of_pos (div_pos (pow_pos (by linarith) _) hH)]
  have e2 : ‖(0 : ℂ) - 1‖ = 1 := by rw [zero_sub, norm_neg, norm_one]
  have e3 : ‖(1 : ℂ) - (1 + (((xsum r n) / Hsum r n : ℝ) : ℂ) * I)‖ =
      xsum r n / Hsum r n := by
    rw [show (1 : ℂ) - (1 + (((xsum r n) / Hsum r n : ℝ) : ℂ) * I) =
        -((((xsum r n) / Hsum r n : ℝ) : ℂ) * I) from by ring, norm_neg, norm_mul,
      Complex.norm_I, mul_one, norm_ofReal', abs_of_pos (div_pos hxpos hH)]
  rw [e1, e2, e3]

/-- The longest edge of the staircase interface. -/
lemma maxE_chainEdges_B {r : ℝ} (hr : 1 < r) {n : ℕ} (hn : 0 < n) :
    maxE (chainEdges (((List.range (2 * n)).map (bfun r)).map (simT r n))) =
      r ^ (2 * n - 1) / Hsum r n := by
  rw [chainEdges_B hr hn]
  have hH : 0 < Hsum r n := Hsum_pos (by linarith) hn
  apply le_antisymm
  · apply maxE_le (div_nonneg (pow_nonneg (by linarith) _) (le_of_lt hH))
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    rw [List.mem_range] at hi
    rw [div_le_div_iff_of_pos_right hH]
    exact pow_le_pow_right₀ (le_of_lt hr) (by omega)
  · apply le_maxE
    rw [List.mem_map]
    exact ⟨2 * n - 2, by rw [List.mem_range]; omega,
      by rw [show 2 * n - 2 + 1 = 2 * n - 1 from by omega]⟩

/-- The longest edge contributed by the top arc is `1`. -/
lemma maxE_arcA {r : ℝ} (hr : 1 < r) {n : ℕ} (hn : 0 < n) :
    maxE [(1 + xsum r (n - 1)) / Hsum r n, 1, 1 / Hsum r n] = 1 := by
  have hH : 0 < Hsum r n := Hsum_pos (by linarith) hn
  have hHe : Hsum r n = r + ysum r (n - 1) := Hsum_eq_add_ysum r hn
  have hb1 : (1 + xsum r (n - 1)) / Hsum r n ≤ 1 := by
    rw [div_le_one hH, hHe, ysum_eq_mul_xsum]
    have hx := xsum_nonneg (le_of_lt hr) (n - 1)
    nlinarith [mul_nonneg (sub_nonneg.2 (le_of_lt hr))
      (by linarith : (0 : ℝ) ≤ 1 + xsum r (n - 1))]
  have hb2 : (Hsum r n)⁻¹ ≤ 1 := by
    rw [← one_div, div_le_one hH]
    have := ysum_nonneg (le_of_lt hr) (n - 1)
    linarith
  apply le_antisymm
  · apply maxE_le zero_le_one
    intro x hx
    simp at hx
    rcases hx with rfl | rfl | rfl
    · exact hb1
    · exact le_refl 1
    · exact hb2
  · exact le_maxE (by simp)

/-- The longest edge contributed by the bottom arc is `xsum / Hsum = r`. -/
lemma maxE_arcC {r : ℝ} (hr : 1 < r) {n : ℕ} (hn : 0 < n) :
    maxE [r ^ (2 * n) / Hsum r n, 1, xsum r n / Hsum r n] = xsum r n / Hsum r n := by
  have hH : 0 < Hsum r n := Hsum_pos (by linarith) hn
  have hxH : xsum r n / Hsum r n = r := by
    rw [xsum_eq_mul_Hsum r n, mul_div_cancel_right₀ _ hH.ne']
  have hb1 : r ^ (2 * n) / Hsum r n ≤ xsum r n / Hsum r n := by
    rw [div_le_div_iff_of_pos_right hH]
    have h2 := Finset.single_le_sum (f := fun i => r ^ (2 * i + 2))
      (fun i _ => pow_nonneg (by linarith : 0 ≤ r) _) (Finset.mem_range.2 (by omega :
      n - 1 < n))
    rwa [show 2 * (n - 1) + 2 = 2 * n from by omega] at h2
  have hb2 : 1 ≤ xsum r n / Hsum r n := by rw [hxH]; exact le_of_lt hr
  apply le_antisymm
  · apply maxE_le (by positivity)
    intro x hx
    simp at hx
    rcases hx with rfl | rfl | rfl
    · exact hb1
    · exact hb2
    · exact le_refl _
  · exact le_maxE (by simp)

/-- The longest edge of the top polygon is `1`. -/
lemma maxE_P {r : ℝ} (hr : 1 < r) {n : ℕ} (hn : 0 < n) :
    maxE (edgeLengths ((((List.range (2 * n)).map (bfun r)).map (simT r n)) ++
      [(((1 + xsum r n) / Hsum r n : ℝ) : ℂ) * I,
        1 + (((1 + xsum r n) / Hsum r n : ℝ) : ℂ) * I])) = 1 := by
  have hH : 0 < Hsum r n := Hsum_pos (by linarith) hn
  rw [← arcA_reverse_tail_dropLast hr hn]
  have hB2 : 2 ≤ (((List.range (2 * n)).map (bfun r)).map (simT r n)).length := by
    simp [List.length_map]
    omega
  have hs4 : (arcA r n hr hn).s.length = 4 := rfl
  have hD2 : 2 ≤ (((arcA r n hr hn).points ((1 + xsum r n) / Hsum r n)).reverse).length := by
    rw [List.length_reverse, BoundaryArc.length_points, hs4]
    norm_num
  have hpts_ne : ((arcA r n hr hn).points ((1 + xsum r n) / Hsum r n)) ≠ [] :=
    ne_nil_of_length_pos (by rw [BoundaryArc.length_points, hs4]; norm_num)
  have hDhead : (((arcA r n hr hn).points ((1 + xsum r n) / Hsum r n)).reverse).head! =
      (((List.range (2 * n)).map (bfun r)).map (simT r n)).getLast! := by
    rw [head!_reverse hpts_ne, BoundaryArc.getLast!_points, sqParam_t1 hr hn, B_getLast hr hn]
  have hDlast : (((arcA r n hr hn).points ((1 + xsum r n) / Hsum r n)).reverse).getLast! =
      (((List.range (2 * n)).map (bfun r)).map (simT r n)).head! := by
    rw [getLast!_reverse hpts_ne, BoundaryArc.head!_points, sqParam_t0 hr hn, B_head hr hn]
  have hbound : r ^ (2 * n - 1) / Hsum r n ≤ 1 := by
    rw [div_le_one hH]
    have h2 := Finset.single_le_sum (f := fun i => r ^ (2 * i + 1))
      (fun i _ => pow_nonneg (by linarith : 0 ≤ r) _) (Finset.mem_range.2 (by omega :
      n - 1 < n))
    rwa [show 2 * (n - 1) + 1 = 2 * n - 1 from by omega] at h2
  rw [edgeLengths_cycle _ _ hB2 hD2 hDhead hDlast, maxE_append, chainEdges_arcA_reverse hr hn,
    maxE_arcA hr hn, maxE_chainEdges_B hr hn]
  exact max_eq_right hbound

/-- The longest edge of the bottom polygon is `xsum / Hsum = r`. -/
lemma maxE_Q {r : ℝ} (hr : 1 < r) {n : ℕ} (hn : 0 < n) :
    maxE (edgeLengths ((((List.range (2 * n)).map (bfun r)).map (simT r n)) ++ [0, 1])) =
      xsum r n / Hsum r n := by
  have hH : 0 < Hsum r n := Hsum_pos (by linarith) hn
  rw [← arcC_tail_dropLast hr hn]
  have hB2 : 2 ≤ (((List.range (2 * n)).map (bfun r)).map (simT r n)).length := by
    simp [List.length_map]
    omega
  have hs4 : (arcC r n hr hn).s.length = 4 := rfl
  have hD2 : 2 ≤ (((arcC r n hr hn).points ((1 + xsum r n) / Hsum r n))).length := by
    rw [BoundaryArc.length_points, hs4]
    norm_num
  have hDhead : (((arcC r n hr hn).points ((1 + xsum r n) / Hsum r n))).head! =
      (((List.range (2 * n)).map (bfun r)).map (simT r n)).getLast! := by
    rw [BoundaryArc.head!_points, sqParam_t1 hr hn, B_getLast hr hn]
  have hDlast : (((arcC r n hr hn).points ((1 + xsum r n) / Hsum r n))).getLast! =
      (((List.range (2 * n)).map (bfun r)).map (simT r n)).head! := by
    rw [BoundaryArc.getLast!_points, sqParam_periodic, sqParam_t0 hr hn, B_head hr hn]
  have hbound : r ^ (2 * n - 1) / Hsum r n ≤ xsum r n / Hsum r n := by
    rw [div_le_div_iff_of_pos_right hH]
    have h2 : r ^ (2 * n) ≤ xsum r n := by
      have h3 := Finset.single_le_sum (f := fun i => r ^ (2 * i + 2))
        (fun i _ => pow_nonneg (by linarith : 0 ≤ r) _) (Finset.mem_range.2 (by omega :
        n - 1 < n))
      rwa [show 2 * (n - 1) + 2 = 2 * n from by omega] at h3
    have h4 : r ^ (2 * n - 1) ≤ r ^ (2 * n) := pow_le_pow_right₀ (le_of_lt hr) (by omega)
    linarith
  rw [edgeLengths_cycle _ _ hB2 hD2 hDhead hDlast, maxE_append, chainEdges_arcC hr hn,
    maxE_arcC hr hn, maxE_chainEdges_B hr hn]
  exact max_eq_right hbound

/-- The two staircase polygons are not congruent. -/
lemma PQ_not_congruent {r : ℝ} (hr : 1 < r) {n : ℕ} (hn : 0 < n) :
    ¬ CycleCongruent
      ((((List.range (2 * n)).map (bfun r)).map (simT r n)) ++
        [(((1 + xsum r n) / Hsum r n : ℝ) : ℂ) * I,
          1 + (((1 + xsum r n) / Hsum r n : ℝ) : ℂ) * I])
      ((((List.range (2 * n)).map (bfun r)).map (simT r n)) ++ [0, 1]) := by
  have hH : 0 < Hsum r n := Hsum_pos (by linarith) hn
  intro hcon
  have hperm := CycleCongruent.edgeLengths_perm hcon
  have e1 := maxE_P hr hn
  have e2 := maxE_Q hr hn
  have h := maxE_of_perm hperm
  rw [e1, e2] at h
  have hxH : xsum r n / Hsum r n = r := by
    rw [xsum_eq_mul_Hsum r n, mul_div_cancel_right₀ _ hH.ne']
  rw [hxH] at h
  linarith

/-- Every aspect ratio `(1 + xsum r n) / Hsum r n` (which exceeds `1 + 1/n`) is
dissectable. -/
lemma dissectable_of_aspect {r : ℝ} (hr : 1 < r) {n : ℕ} (hn : 0 < n) :
    Dissectable ((1 + xsum r n) / Hsum r n) := by
  refine ⟨((List.range (2 * n)).map (bfun r)).map (simT r n),
    1 + xsum r n / (1 + xsum r n), 4 - r ^ (2 * n) / (1 + xsum r n),
    arcA r n hr hn, arcC r n hr hn, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [List.length_map]
    omega
  · rw [B_head hr hn, sqParam_t0 hr hn]
  · rw [B_getLast hr hn, sqParam_t1 hr hn]
  · exact B_interior hr hn
  · exact B_chain hr hn
  · show CycleSimilar _ _ ∧ ¬ CycleCongruent _ _
    rw [arcA_reverse_tail_dropLast hr hn, arcC_tail_dropLast hr hn]
    exact ⟨PQ_similar hr hn, PQ_not_congruent hr hn⟩

/-- Every `k > 1` is dissectable. -/
lemma dissectable_gt_one {k : ℝ} (hk : 1 < k) : Dissectable k := by
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show 0 < k - 1 by linarith)
  obtain ⟨r, hr, hrr⟩ := exists_ratio (n := n + 1) (k := k) (by omega) (by
    push_cast
    linarith [hn])
  rw [← hrr]
  exact dissectable_of_aspect hr (by omega)

/-! ### Transport along the similarity `z ↦ (I/k) * star z` -/

/-- The common shape of `CycleSimilar` and `CycleCongruent`, abstracted over the
condition on the linear part. -/
def CycleRel (cond : ℂ → Prop) (V W : List ℂ) : Prop :=
  ∃ (α β : ℂ) (m : ℕ), cond α ∧
    (W = (V.map fun z => α * z + β).rotate m ∨ W = (V.map fun z => α * star z + β).rotate m)

lemma CycleSimilar.cycleRel {V W : List ℂ} (h : CycleSimilar V W) : CycleRel (· ≠ 0) V W := h

lemma CycleCongruent.cycleRel {V W : List ℂ} (h : CycleCongruent V W) :
    CycleRel (fun α => ‖α‖ = 1) V W := h

lemma CycleRel.similar {V W : List ℂ} (h : CycleRel (· ≠ 0) V W) : CycleSimilar V W := h

lemma CycleRel.congruent {V W : List ℂ} (h : CycleRel (fun α => ‖α‖ = 1) V W) :
    CycleCongruent V W := h

/-- Rotating by the length plus a fixed offset. -/
lemma rotate_add_length (l : List ℂ) (n : ℕ) : l.rotate (n + l.length) = l.rotate n := by
  rw [← List.rotate_rotate, show l.length = (l.rotate n).length from
    (List.length_rotate _ _).symm, List.rotate_length]

/-- Rotating by a multiple of the length plus a fixed offset. -/
lemma rotate_add_length_mul (l : List ℂ) (n c : ℕ) : l.rotate (n + l.length * c) = l.rotate n := by
  induction c with
  | zero => simp
  | succ c ih =>
    rw [show n + l.length * (c + 1) = (n + l.length * c) + l.length from by ring,
      rotate_add_length, ih]

/-- Mapping both cycles by an orientation-reversing similarity preserves the
relation (the conjugated map has the same norm on its linear part). -/
lemma CycleRel.map_similar {cond : ℂ → Prop} {V W : List ℂ} {T : ℂ → ℂ} {γ δ : ℂ} (hγ : γ ≠ 0)
    (hT : ∀ z, T z = γ * star z + δ)
    (hc : ∀ α, cond α → cond (γ * star α * γ⁻¹))
    (hc' : ∀ α, cond α → cond (γ * star α / star γ))
    (h : CycleRel cond V W) : CycleRel cond (V.map T) (W.map T) := by
  obtain ⟨α, β, m, hcond, hcase⟩ := h
  have hγs : star γ ≠ 0 := by rwa [star_ne_zero]
  rcases hcase with hcase | hcase
  · refine ⟨γ * star α * γ⁻¹, γ * star β + δ - (γ * star α * γ⁻¹) * δ, m, hc α hcond,
      Or.inl ?_⟩
    have hα' : (γ * star α * γ⁻¹) * γ = γ * star α := by
      rw [mul_assoc, inv_mul_cancel₀ hγ, mul_one]
    have key : ∀ z, T (α * z + β) =
        (γ * star α * γ⁻¹) * T z + (γ * star β + δ - (γ * star α * γ⁻¹) * δ) := by
      intro z
      rw [hT, hT]
      simp only [star_add, star_mul']
      have e1 : (γ * star α * γ⁻¹) * (γ * star z + δ) +
          (γ * star β + δ - (γ * star α * γ⁻¹) * δ) = γ * (star α * star z + star β) + δ := by
        rw [mul_add, ← mul_assoc (γ * star α * γ⁻¹) γ (star z), hα']
        ring
      rw [e1]
    rw [hcase, List.map_rotate, List.map_map, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a ha
    rw [Function.comp_apply, Function.comp_apply]
    exact key a
  · refine ⟨γ * star α / star γ, γ * star β + δ - (γ * star α / star γ) * star δ, m,
      hc' α hcond, Or.inr ?_⟩
    have hα' : (γ * star α / star γ) * star γ = γ * star α := div_mul_cancel₀ _ hγs
    have key : ∀ z, T (α * star z + β) =
        (γ * star α / star γ) * star (T z) + (γ * star β + δ - (γ * star α / star γ) * star δ) := by
      intro z
      rw [hT, hT]
      simp only [star_add, star_mul', star_star]
      have e1 : (γ * star α / star γ) * (star γ * z + star δ) +
          (γ * star β + δ - (γ * star α / star γ) * star δ) = γ * (star α * z + star β) + δ := by
        rw [mul_add, ← mul_assoc (γ * star α / star γ) (star γ) z, hα']
        ring
      rw [e1]
    rw [hcase, List.map_rotate, List.map_map, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a ha
    rw [Function.comp_apply, Function.comp_apply]
    exact key a

/-- Reversing both cycles preserves the relation. -/
lemma CycleRel.reverse {cond : ℂ → Prop} {V W : List ℂ} (h : CycleRel cond V W) :
    CycleRel cond V.reverse W.reverse := by
  obtain ⟨α, β, m, hcond, hcase⟩ := h
  rcases hcase with hcase | hcase
  · refine ⟨α, β, V.length - m % V.length, hcond, Or.inl ?_⟩
    rw [hcase, List.reverse_rotate, List.length_map, ← List.map_reverse]
  · refine ⟨α, β, V.length - m % V.length, hcond, Or.inr ?_⟩
    rw [hcase, List.reverse_rotate, List.length_map, ← List.map_reverse]

/-- Rotating the first cycle preserves the relation. -/
lemma CycleRel.rotate_left {cond : ℂ → Prop} {V W : List ℂ} (j : ℕ) (h : CycleRel cond V W) :
    CycleRel cond (V.rotate j) W := by
  obtain ⟨α, β, m, hcond, hcase⟩ := h
  rcases hcase with hcase | hcase
  · by_cases hV : V = []
    · subst hV
      simp only [List.map_nil, List.rotate_nil] at hcase
      subst hcase
      exact ⟨α, β, 0, hcond, Or.inl (by simp)⟩
    · have hL : 0 < (V.map fun z => α * z + β).length := by
        rwa [List.length_map, List.length_pos_iff]
      have h2 := Nat.mod_add_div j (V.map fun z => α * z + β).length
      have h3 := Nat.mod_lt j hL
      refine ⟨α, β, m + ((V.map fun z => α * z + β).length - j %
        (V.map fun z => α * z + β).length), hcond, Or.inl ?_⟩
      rw [hcase, List.map_rotate, List.rotate_rotate,
        show j + (m + ((V.map fun z => α * z + β).length -
            j % (V.map fun z => α * z + β).length)) =
          (m + (V.map fun z => α * z + β).length) +
            (V.map fun z => α * z + β).length * (j / (V.map fun z => α * z + β).length) from by
          omega, rotate_add_length_mul, rotate_add_length]
  · by_cases hV : V = []
    · subst hV
      simp only [List.map_nil, List.rotate_nil] at hcase
      subst hcase
      exact ⟨α, β, 0, hcond, Or.inl (by simp)⟩
    · have hL : 0 < (V.map fun z => α * star z + β).length := by
        rwa [List.length_map, List.length_pos_iff]
      have h2 := Nat.mod_add_div j (V.map fun z => α * star z + β).length
      have h3 := Nat.mod_lt j hL
      refine ⟨α, β, m + ((V.map fun z => α * star z + β).length - j %
        (V.map fun z => α * star z + β).length), hcond, Or.inr ?_⟩
      rw [hcase, List.map_rotate, List.rotate_rotate,
        show j + (m + ((V.map fun z => α * star z + β).length -
            j % (V.map fun z => α * star z + β).length)) =
          (m + (V.map fun z => α * star z + β).length) +
            (V.map fun z => α * star z + β).length * (j / (V.map fun z => α * star z + β).length)
          from by
          omega, rotate_add_length_mul, rotate_add_length]

/-- Rotating the second cycle preserves the relation. -/
lemma CycleRel.rotate_right {cond : ℂ → Prop} {V W : List ℂ} (j : ℕ) (h : CycleRel cond V W) :
    CycleRel cond V (W.rotate j) := by
  obtain ⟨α, β, m, hcond, hcase⟩ := h
  rcases hcase with hcase | hcase
  · exact ⟨α, β, m + j, hcond, Or.inl (by rw [hcase, List.rotate_rotate])⟩
  · exact ⟨α, β, m + j, hcond, Or.inr (by rw [hcase, List.rotate_rotate])⟩

/-- A relation between a rotation of the first cycle and the second descends to
the unrotated first cycle. -/
lemma CycleRel.rotate_left_elim {cond : ℂ → Prop} {V W : List ℂ} {j : ℕ}
    (h : CycleRel cond (V.rotate j) W) : CycleRel cond V W := by
  obtain ⟨α, β, m, hcond, hcase⟩ := h
  rcases hcase with hcase | hcase
  · exact ⟨α, β, j + m, hcond, Or.inl (by rw [hcase, List.map_rotate, List.rotate_rotate])⟩
  · exact ⟨α, β, j + m, hcond, Or.inr (by rw [hcase, List.map_rotate, List.rotate_rotate])⟩

/-- A relation between the first cycle and a rotation of the second descends to
the unrotated second cycle. -/
lemma CycleRel.rotate_right_elim {cond : ℂ → Prop} {V W : List ℂ} {j : ℕ} (hW : W ≠ [])
    (h : CycleRel cond V (W.rotate j)) : CycleRel cond V W := by
  obtain ⟨α, β, m, hcond, hcase⟩ := h
  have hL : 0 < W.length := List.length_pos_iff.2 hW
  have e : W = (W.rotate j).rotate (W.length - j % W.length) := by
    have h2 := Nat.mod_add_div j W.length
    have h3 := Nat.mod_lt j hL
    rw [List.rotate_rotate, show j + (W.length - j % W.length) =
        W.length + W.length * (j / W.length) from by
      omega, rotate_add_length_mul, List.rotate_length]
  rcases hcase with hcase | hcase
  · refine ⟨α, β, m + (W.length - j % W.length), hcond, Or.inl ?_⟩
    conv_lhs => rw [e]
    rw [hcase, List.rotate_rotate]
  · refine ⟨α, β, m + (W.length - j % W.length), hcond, Or.inr ?_⟩
    conv_lhs => rw [e]
    rw [hcase, List.rotate_rotate]

/-- The similarity `(I/k) * star z`, mapping the rectangle `[0,1]×[0,k]` onto
`[0,1]×[0,1/k]`. -/
noncomputable def Tsim (k : ℝ) (z : ℂ) : ℂ := (I / (k : ℂ)) * star z

/-- The inverse of `Tsim k`. -/
noncomputable def TsimInv (k : ℝ) (w : ℂ) : ℂ := (k : ℂ) * I * star w

lemma Tsim_TsimInv {k : ℝ} (hk : k ≠ 0) (w : ℂ) : Tsim k (TsimInv k w) = w := by
  have hk' : ((k : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hk
  apply Complex.ext_iff.2
  constructor <;>
    simp [Tsim, TsimInv, Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im,
      Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.neg_re, Complex.neg_im] <;>
    field_simp [hk] <;>
    ring

lemma TsimInv_Tsim {k : ℝ} (hk : k ≠ 0) (z : ℂ) : TsimInv k (Tsim k z) = z := by
  have hk' : ((k : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hk
  apply Complex.ext_iff.2
  constructor <;>
    simp [Tsim, TsimInv, Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im,
      Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.neg_re, Complex.neg_im] <;>
    field_simp [hk] <;>
    ring

lemma Tsim_injective {k : ℝ} (hk : k ≠ 0) : Function.Injective (Tsim k) := by
  intro z w h
  have hk' : ((k : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hk
  simp only [Tsim] at h
  have h2 := mul_left_cancel₀ (div_ne_zero Complex.I_ne_zero hk') h
  exact star_injective h2

lemma Tsim_add (k : ℝ) (z w : ℂ) : Tsim k (z + w) = Tsim k z + Tsim k w := by
  simp only [Tsim, star_add, mul_add]

lemma Tsim_sub (k : ℝ) (z w : ℂ) : Tsim k (z - w) = Tsim k z - Tsim k w := by
  simp only [Tsim, star_sub, mul_sub]

lemma Tsim_smul (k : ℝ) (s : ℝ) (z : ℂ) : Tsim k (s • z) = s • Tsim k z := by
  simp only [Tsim, Complex.real_smul, star_mul']
  rw [show star (s : ℂ) = (s : ℂ) from by simp]
  ring

lemma Tsim_re {k : ℝ} (hk : 0 < k) (z : ℂ) : (Tsim k z).re = z.im / k := by
  simp [Tsim, Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im, Complex.I_re,
    Complex.I_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
  field_simp [hk.ne']

lemma Tsim_im {k : ℝ} (hk : 0 < k) (z : ℂ) : (Tsim k z).im = z.re / k := by
  simp [Tsim, Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im, Complex.I_re,
    Complex.I_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
  field_simp [hk.ne']

/-- The action of `Tsim k` on the corners of the `k`-rectangle: `corner k c` goes
to `corner (1/k) (-c)`. -/
lemma T_corner {k : ℝ} (hk : 0 < k) (c : ℤ) : Tsim k (corner k c) = corner k⁻¹ (-c) := by
  have hk' : ((k : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  have hkc : ((k⁻¹ : ℝ) : ℂ) = (k : ℂ)⁻¹ := by norm_cast
  have hstarI : star ((k : ℂ) * I) = -((k : ℂ) * I) := by
    simp [star_mul', Complex.conj_ofReal, Complex.conj_I, ← Complex.ofReal_mul]
  have hstar1 : star (1 + (k : ℂ) * I) = 1 - (k : ℂ) * I := by
    simp only [star_add, star_one, star_mul', Complex.star_def, Complex.conj_ofReal,
      Complex.conj_I]
    ring
  rcases (show c % 4 = 0 ∨ c % 4 = 1 ∨ c % 4 = 2 ∨ c % 4 = 3 from by omega) with
    h | h | h | h
  · have h' : (-c) % 4 = 0 := by omega
    rw [show corner k c = 0 from by simp [corner, h], show corner k⁻¹ (-c) = 0 from by
      simp [corner, h']]
    simp [Tsim]
  · have h' : (-c) % 4 = 3 := by omega
    rw [show corner k c = 1 from by simp [corner, h],
      show corner k⁻¹ (-c) = ((k⁻¹ : ℝ) : ℂ) * I from by simp [corner, h']]
    simp only [Tsim, star_one, mul_one]
    rw [div_eq_mul_inv, ← hkc, mul_comm]
  · have h' : (-c) % 4 = 2 := by omega
    rw [show corner k c = 1 + (k : ℂ) * I from by simp [corner, h],
      show corner k⁻¹ (-c) = 1 + ((k⁻¹ : ℝ) : ℂ) * I from by simp [corner, h']]
    simp only [Tsim]
    rw [hstar1, mul_sub, mul_one, ← mul_assoc, div_mul_cancel₀ _ hk', Complex.I_mul_I,
      div_eq_mul_inv, ← hkc]
    ring
  · have h' : (-c) % 4 = 1 := by omega
    rw [show corner k c = (k : ℂ) * I from by simp [corner, h],
      show corner k⁻¹ (-c) = 1 from by simp [corner, h']]
    simp only [Tsim]
    rw [hstarI, mul_neg, ← mul_assoc, div_mul_cancel₀ _ hk', Complex.I_mul_I, neg_neg]

/-- The action of `Tsim k` on the boundary parametrization. -/
lemma T_sqParam {k : ℝ} (hk : 0 < k) (t : ℝ) :
    Tsim k (sqParam k t) = sqParam k⁻¹ (-t) := by
  rw [show sqParam k t = corner k ⌊t⌋ + (t - (⌊t⌋ : ℝ)) • (corner k (⌊t⌋ + 1) - corner k ⌊t⌋)
    from rfl]
  rw [Tsim_add, Tsim_smul, Tsim_sub, T_corner hk, T_corner hk]
  by_cases ht : t = (⌊t⌋ : ℝ)
  · have e : ⌊-t⌋ = -⌊t⌋ := by
      rw [show -t = ((-⌊t⌋ : ℤ) : ℝ) from by push_cast; linarith [ht], Int.floor_intCast]
    rw [show sqParam k⁻¹ (-t) = corner k⁻¹ ⌊-t⌋ + (-t - (⌊-t⌋ : ℝ)) •
        (corner k⁻¹ (⌊-t⌋ + 1) - corner k⁻¹ ⌊-t⌋) from rfl, e,
      show (-t - ((-⌊t⌋ : ℤ) : ℝ)) = (0 : ℝ) from by push_cast; linarith [ht], zero_smul,
      add_zero, show (t - (⌊t⌋ : ℝ)) = (0 : ℝ) from by linarith [ht], zero_smul, add_zero]
  · have e : ⌊-t⌋ = -⌊t⌋ - 1 := by
      rw [Int.floor_eq_iff]
      constructor
      · have h2 := Int.lt_floor_add_one t
        push_cast
        linarith
      · have h2 : (⌊t⌋ : ℝ) < t := lt_of_le_of_ne (Int.floor_le t) (fun h => ht h.symm)
        push_cast
        linarith
    rw [show sqParam k⁻¹ (-t) = corner k⁻¹ ⌊-t⌋ + (-t - (⌊-t⌋ : ℝ)) •
        (corner k⁻¹ (⌊-t⌋ + 1) - corner k⁻¹ ⌊-t⌋) from rfl, e]
    have e2 : (-t - ((-⌊t⌋ - 1 : ℤ) : ℝ)) = 1 - (t - (⌊t⌋ : ℝ)) := by
      push_cast
      ring
    have e3 : (-⌊t⌋ - 1 : ℤ) + 1 = -⌊t⌋ := by omega
    have e4 : -(⌊t⌋ + 1) = -⌊t⌋ - 1 := by omega
    rw [e2, e3, e4]
    have expand1 : ∀ (A B : ℂ) (f : ℝ), A + f • (B - A) = (1 - f) • A + f • B := by
      intro A B f
      module
    have expand2 : ∀ (A B : ℂ) (f : ℝ), B + (1 - f) • (A - B) = (1 - f) • A + f • B := by
      intro A B f
      module
    rw [expand1, expand2]

/-- The `≠` chain condition is symmetric. -/
lemma isChain_ne_flip {l : List ℂ} (h : l.IsChain (· ≠ ·)) : l.IsChain (fun a b => b ≠ a) := by
  induction l with
  | nil => exact List.isChain_nil
  | cons a l ih =>
    cases l with
    | nil => exact List.isChain_singleton _
    | cons b l =>
      rw [List.isChain_cons_cons]
      exact ⟨(List.isChain_cons_cons.1 h).1.symm, ih (List.IsChain.tail h)⟩

/-- Mapping a chain by an injective function preserves the chain condition. -/
lemma isChain_map_ne_of_inj {l : List ℂ} {T : ℂ → ℂ} (hT : Function.Injective T)
    (h : l.IsChain (· ≠ ·)) : (l.map T).IsChain (· ≠ ·) := by
  induction l with
  | nil => exact List.isChain_nil
  | cons a l ih =>
    cases l with
    | nil => exact List.isChain_singleton _
    | cons b l =>
      rw [List.map_cons, List.map_cons, List.isChain_cons_cons]
      have hab := (List.isChain_cons_cons.1 h).1
      exact ⟨fun hcon => hab (hT hcon), ih (List.IsChain.tail h)⟩

/-- Negating reverses a decreasing chain into an increasing one. -/
lemma isChain_map_neg {l : List ℝ} (h : l.IsChain fun x y => y < x) :
    (l.map fun t => -t).IsChain (· < ·) := by
  induction l with
  | nil => exact List.isChain_nil
  | cons a l ih =>
    cases l with
    | nil => exact List.isChain_singleton _
    | cons b l =>
      rw [List.map_cons, List.map_cons, List.isChain_cons_cons]
      have hab := (List.isChain_cons_cons.1 h).1
      exact ⟨by linarith [hab], ih (List.IsChain.tail h)⟩

/-- Negating transports the same-side condition. -/
lemma isChain_map_neg_side {l : List ℝ}
    (h : l.IsChain fun x y => ∃ c : ℤ, (c : ℝ) ≤ y ∧ x ≤ c + 1) :
    (l.map fun t => -t).IsChain fun x y => ∃ c : ℤ, (c : ℝ) ≤ x ∧ y ≤ c + 1 := by
  induction l with
  | nil => exact List.isChain_nil
  | cons a l ih =>
    cases l with
    | nil => exact List.isChain_singleton _
    | cons b l =>
      rw [List.map_cons, List.map_cons, List.isChain_cons_cons]
      obtain ⟨c, hc1, hc2⟩ := (List.isChain_cons_cons.1 h).1
      refine ⟨⟨-(c + 1), by push_cast; linarith, by push_cast; linarith⟩,
        ih (List.IsChain.tail h)⟩

/-- Adding `4` preserves an increasing chain. -/
lemma isChain_map_add4 {l : List ℝ} (h : l.IsChain (· < ·)) :
    (l.map fun t => t + 4).IsChain (· < ·) := by
  induction l with
  | nil => exact List.isChain_nil
  | cons a l ih =>
    cases l with
    | nil => exact List.isChain_singleton _
    | cons b l =>
      rw [List.map_cons, List.map_cons, List.isChain_cons_cons]
      have hab := (List.isChain_cons_cons.1 h).1
      exact ⟨by linarith [hab], ih (List.IsChain.tail h)⟩

/-- Adding `4` transports the same-side condition. -/
lemma isChain_map_add4_side {l : List ℝ}
    (h : l.IsChain fun x y => ∃ c : ℤ, (c : ℝ) ≤ x ∧ y ≤ c + 1) :
    (l.map fun t => t + 4).IsChain fun x y => ∃ c : ℤ, (c : ℝ) ≤ x ∧ y ≤ c + 1 := by
  induction l with
  | nil => exact List.isChain_nil
  | cons a l ih =>
    cases l with
    | nil => exact List.isChain_singleton _
    | cons b l =>
      rw [List.map_cons, List.map_cons, List.isChain_cons_cons]
      obtain ⟨c, hc1, hc2⟩ := (List.isChain_cons_cons.1 h).1
      refine ⟨⟨c + 4, by push_cast; linarith, by push_cast; linarith⟩,
        ih (List.IsChain.tail h)⟩

/-- The boundary arc traversed backwards with negated parameters. -/
def BoundaryArc.negReverse {a b : ℝ} (A : BoundaryArc a b) : BoundaryArc (-b) (-a) where
  s := (A.s.reverse).map fun t => -t
  hne := by simp [A.hne]
  hhead := by
    show ((A.s.reverse).map fun t => -t).head _ = -b
    rw [List.head_map, List.head_reverse, A.hlast]
  hlast := by
    show ((A.s.reverse).map fun t => -t).getLast _ = -a
    rw [List.getLast_map, List.getLast_reverse, A.hhead]
  hmono := isChain_map_neg (List.isChain_reverse.2 A.hmono)
  hside := isChain_map_neg_side (List.isChain_reverse.2 A.hside)
  hint := by
    intro x hx h1 h2
    rw [List.mem_map] at hx
    obtain ⟨u, hu, rfl⟩ := hx
    rw [List.mem_reverse] at hu
    have hu1 : u ≠ a := fun h => h2 (by rw [h])
    have hu2 : u ≠ b := fun h => h1 (by rw [h])
    obtain ⟨c, hc⟩ := A.hint u hu hu1 hu2
    exact ⟨-c, by rw [hc]; push_cast; ring⟩
  hcover := by
    intro c h1 h2
    have h3 : ((-c : ℤ) : ℝ) ∈ A.s := A.hcover (-c) (by push_cast; linarith)
      (by push_cast; linarith)
    rw [List.mem_map]
    exact ⟨((-c : ℤ) : ℝ), List.mem_reverse.2 h3, by push_cast; ring⟩

/-- Shifting all parameters of a boundary arc by `4`. -/
def BoundaryArc.shift4 {a b : ℝ} (A : BoundaryArc a b) : BoundaryArc (a + 4) (b + 4) where
  s := (A.s).map fun t => t + 4
  hne := by simp [A.hne]
  hhead := by
    show ((A.s).map fun t => t + 4).head _ = a + 4
    rw [List.head_map, A.hhead]
  hlast := by
    show ((A.s).map fun t => t + 4).getLast _ = b + 4
    rw [List.getLast_map, A.hlast]
  hmono := isChain_map_add4 A.hmono
  hside := isChain_map_add4_side A.hside
  hint := by
    intro x hx h1 h2
    rw [List.mem_map] at hx
    obtain ⟨u, hu, rfl⟩ := hx
    have hu1 : u ≠ a := fun h => h1 (by rw [h])
    have hu2 : u ≠ b := fun h => h2 (by rw [h])
    obtain ⟨c, hc⟩ := A.hint u hu hu1 hu2
    exact ⟨c + 4, by rw [hc]; push_cast; ring⟩
  hcover := by
    intro c h1 h2
    have h3 : (((c - 4 : ℤ)) : ℝ) ∈ A.s := A.hcover (c - 4) (by push_cast; linarith)
      (by push_cast; linarith)
    rw [List.mem_map]
    exact ⟨((c - 4 : ℤ) : ℝ), h3, by push_cast; ring⟩

/-- The points of the negated-reversed arc are the `Tsim`-images of the reversed
points of the original arc. -/
lemma BoundaryArc.negReverse_points {k : ℝ} (hk : 0 < k) {a b : ℝ} (A : BoundaryArc a b) :
    (A.negReverse).points k⁻¹ = ((A.points k).map (Tsim k)).reverse := by
  rw [show (A.negReverse).points k⁻¹ = ((A.s.reverse).map fun t => -t).map (sqParam k⁻¹)
      from rfl,
    show (A.points k) = A.s.map (sqParam k) from rfl, List.map_map, List.map_map,
    ← List.map_reverse]
  apply List.map_congr_left
  intro t ht
  rw [Function.comp_apply, Function.comp_apply]
  exact (T_sqParam hk t).symm

/-- Shifting an arc by `4` does not change its points. -/
lemma BoundaryArc.shift4_points {k : ℝ} {a b : ℝ} (A : BoundaryArc a b) :
    (A.shift4).points k = A.points k := by
  rw [show (A.shift4).points k = ((A.s).map fun t => t + 4).map (sqParam k) from rfl,
    show (A.points k) = A.s.map (sqParam k) from rfl, List.map_map]
  apply List.map_congr_left
  intro t ht
  rw [Function.comp_apply]
  exact sqParam_periodic k t

/-- Dropping the last element of a reversed list. -/
lemma dropLast_reverse {α : Type*} (l : List α) : l.reverse.dropLast = l.tail.reverse := by
  have h := List.tail_reverse (l := l.reverse)
  rw [List.reverse_reverse] at h
  rw [← List.reverse_reverse l.reverse.dropLast, ← h]

/-- Taking the tail and dropping the last element commute. -/
lemma tail_dropLast {α : Type*} (l : List α) : l.tail.dropLast = l.dropLast.tail := by
  cases l with
  | nil => rfl
  | cons a l =>
    cases l with
    | nil => rfl
    | cons b l => rfl

/-- Reversing commutes with taking the interior of a list. -/
lemma reverse_tail_dropLast {α : Type*} (l : List α) :
    (l.tail.dropLast).reverse = l.reverse.tail.dropLast := by
  rw [tail_dropLast, ← dropLast_reverse, ← List.tail_reverse]

/-- Mapping commutes with taking the interior of a list. -/
lemma map_tail_dropLast (l : List ℂ) (f : ℂ → ℂ) :
    (l.tail.dropLast).map f = (l.map f).tail.dropLast := by
  rw [List.map_dropLast, List.map_tail]

/-- Mapping commutes with taking the interior of a reversed list. -/
lemma map_reverse_tail_dropLast (l : List ℂ) (f : ℂ → ℂ) :
    (l.reverse.tail.dropLast).map f = (l.map f).reverse.tail.dropLast := by
  rw [List.map_dropLast, List.map_tail, List.map_reverse]

/-- Transporting a boundary arc along equalities of its endpoints. -/
def BoundaryArc.cast {a b a' b' : ℝ} (ha : a' = a) (hb : b' = b) (A : BoundaryArc a b) :
    BoundaryArc a' b' where
  s := A.s
  hne := A.hne
  hhead := by rw [ha]; exact A.hhead
  hlast := by rw [hb]; exact A.hlast
  hmono := A.hmono
  hside := A.hside
  hint := by
    intro x hx h1 h2
    rw [ha] at h1
    rw [hb] at h2
    exact A.hint x hx h1 h2
  hcover := by rw [ha, hb]; exact A.hcover

/-- A dissection of the `k`-rectangle transports to a dissection of the
`1/k`-rectangle via the similarity `Tsim k`. -/
lemma dissectable_inverse {k : ℝ} (hk : 0 < k) (h : Dissectable k) : Dissectable k⁻¹ := by
  obtain ⟨B, t₀, t₁, A, C, hB2, hBh, hBl, hBint, hBchain, hsim, hncong⟩ := h
  have hk' : k ≠ 0 := hk.ne'
  have hBne : B ≠ [] := ne_nil_of_length_pos (by omega)
  refine ⟨(B.map (Tsim k)).reverse, -t₁, -t₀, A.negReverse,
    BoundaryArc.cast (show -t₀ = -(t₀ + 4) + 4 from by ring) rfl (C.negReverse).shift4,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [List.length_reverse, List.length_map]
    exact hB2
  · rw [head!_reverse (ne_nil_of_length_pos (by rw [List.length_map]; omega)),
      getLast!_map _ hBne, hBl, T_sqParam hk]
  · rw [getLast!_reverse (ne_nil_of_length_pos (by rw [List.length_map]; omega)),
      head!_map _ hBne, hBh, T_sqParam hk]
  · intro z hz
    have hB'td : ((B.map (Tsim k)).reverse).tail.dropLast =
        (B.tail.dropLast.reverse).map (Tsim k) := by
      rw [List.tail_reverse, dropLast_reverse, ← List.map_dropLast, ← List.map_tail,
        ← tail_dropLast, ← List.map_reverse]
    rw [hB'td, List.mem_map] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    rw [List.mem_reverse] at hw
    obtain ⟨h1, h2, h3, h4⟩ := hBint w hw
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [Tsim_re hk]
      exact div_pos h3 hk
    · rw [Tsim_re hk, div_lt_one hk]
      exact h4
    · rw [Tsim_im hk]
      exact div_pos h1 hk
    · rw [Tsim_im hk, div_lt_iff₀ hk, inv_mul_cancel₀ hk']
      exact h2
  · exact List.isChain_reverse.2 (isChain_ne_flip (isChain_map_ne_of_inj (Tsim_injective hk') hBchain))
  · show CycleSimilar _ _ ∧ ¬ CycleCongruent _ _
    have hApts : ((A.negReverse).points k⁻¹).reverse = (A.points k).map (Tsim k) := by
      rw [BoundaryArc.negReverse_points hk, List.reverse_reverse]
    have hCpts : ((BoundaryArc.cast (show -t₀ = -(t₀ + 4) + 4 from by ring) rfl
        (C.negReverse).shift4).points k⁻¹).reverse = (C.points k).map (Tsim k) := by
      rw [show (BoundaryArc.cast _ _ _).points k⁻¹ = ((C.negReverse).shift4).points k⁻¹
        from rfl, BoundaryArc.shift4_points, BoundaryArc.negReverse_points hk,
        List.reverse_reverse]
    have hTP : (B ++ (A.points k).reverse.tail.dropLast).map (Tsim k) =
        (B.map (Tsim k)) ++ ((A.negReverse).points k⁻¹).tail.dropLast := by
      rw [List.map_append, map_reverse_tail_dropLast, ← hApts, List.reverse_reverse]
    have hTPrev : ((B ++ (A.points k).reverse.tail.dropLast).map (Tsim k)).reverse =
        (((A.negReverse).points k⁻¹).tail.dropLast).reverse ++ (B.map (Tsim k)).reverse := by
      rw [hTP, List.reverse_append]
    have hProt : (((B ++ (A.points k).reverse.tail.dropLast).map (Tsim k)).reverse).rotate
        ((((A.negReverse).points k⁻¹).tail.dropLast).reverse).length =
        (B.map (Tsim k)).reverse ++ ((A.negReverse).points k⁻¹).reverse.tail.dropLast := by
      rw [hTPrev, List.rotate_append_length_eq, reverse_tail_dropLast]
    have hTQ : (B ++ (C.points k).tail.dropLast).map (Tsim k) =
        (B.map (Tsim k)) ++ ((BoundaryArc.cast (show -t₀ = -(t₀ + 4) + 4 from by ring) rfl
        (C.negReverse).shift4).points k⁻¹).reverse.tail.dropLast := by
      rw [List.map_append, map_tail_dropLast, ← hCpts]
    have hTQrev : ((B ++ (C.points k).tail.dropLast).map (Tsim k)).reverse =
        (((BoundaryArc.cast (show -t₀ = -(t₀ + 4) + 4 from by ring) rfl
        (C.negReverse).shift4).points k⁻¹).reverse.tail.dropLast).reverse ++
        (B.map (Tsim k)).reverse := by
      rw [hTQ, List.reverse_append]
    have hQrot : (((B ++ (C.points k).tail.dropLast).map (Tsim k)).reverse).rotate
        ((((BoundaryArc.cast (show -t₀ = -(t₀ + 4) + 4 from by ring) rfl
        (C.negReverse).shift4).points k⁻¹).reverse.tail.dropLast).reverse).length =
        (B.map (Tsim k)).reverse ++ ((BoundaryArc.cast (show -t₀ = -(t₀ + 4) + 4 from by ring)
        rfl (C.negReverse).shift4).points k⁻¹).tail.dropLast := by
      rw [hTQrev, List.rotate_append_length_eq, reverse_tail_dropLast, List.reverse_reverse]
    have hmapT : ∀ (l : List ℂ), (l.map (Tsim k)).map (TsimInv k) = l := by
      intro l
      rw [List.map_map]
      exact (List.map_congr_left (fun x _ => TsimInv_Tsim hk' x)).trans (List.map_id' l)
    constructor
    · have hγ : (I / (k : ℂ)) ≠ 0 := div_ne_zero Complex.I_ne_zero (by exact_mod_cast hk')
      have hγs : star (I / (k : ℂ)) ≠ 0 := by rwa [star_ne_zero]
      have hsimrel : CycleRel (· ≠ 0)
          ((B ++ (A.points k).reverse.tail.dropLast).map (Tsim k)).reverse
          ((B ++ (C.points k).tail.dropLast).map (Tsim k)).reverse :=
        CycleRel.reverse (CycleRel.map_similar (δ := 0) hγ (fun z => by simp [Tsim])
          (fun α hα => mul_ne_zero (mul_ne_zero hγ (by rwa [star_ne_zero])) (inv_ne_zero hγ))
          (fun α hα => div_ne_zero (mul_ne_zero hγ (by rwa [star_ne_zero])) hγs)
          (CycleSimilar.cycleRel hsim))
      have hsimrel2 := CycleRel.rotate_left
        ((((A.negReverse).points k⁻¹).tail.dropLast).reverse).length hsimrel
      rw [hProt] at hsimrel2
      have hsimrel3 := CycleRel.rotate_right
        ((((BoundaryArc.cast (show -t₀ = -(t₀ + 4) + 4 from by ring) rfl
        (C.negReverse).shift4).points k⁻¹).reverse.tail.dropLast).reverse).length hsimrel2
      rw [hQrot] at hsimrel3
      exact CycleRel.similar hsimrel3
    · intro hcon
      have hγ' : ((k : ℂ) * I) ≠ 0 := mul_ne_zero (by exact_mod_cast hk') Complex.I_ne_zero
      have hγ's : star ((k : ℂ) * I) ≠ 0 := by rwa [star_ne_zero]
      have hnorm : ∀ α : ℂ, ‖α‖ = 1 → ‖((k : ℂ) * I) * star α * ((k : ℂ) * I)⁻¹‖ = 1 := by
        intro α hα
        rw [norm_mul, norm_mul, norm_star, hα, norm_inv, mul_one,
          mul_inv_cancel₀ (norm_pos_iff.2 hγ').ne']
      have hnorm' : ∀ α : ℂ, ‖α‖ = 1 → ‖((k : ℂ) * I) * star α / star ((k : ℂ) * I)‖ = 1 := by
        intro α hα
        rw [norm_div, norm_mul, norm_star, norm_star, hα, mul_one,
          div_self (norm_pos_iff.2 hγ').ne']
      have hrel : CycleRel (fun α => ‖α‖ = 1)
          (((B.map (Tsim k)).reverse ++
            ((A.negReverse).points k⁻¹).reverse.tail.dropLast).map (TsimInv k))
          (((B.map (Tsim k)).reverse ++
            ((BoundaryArc.cast (show -t₀ = -(t₀ + 4) + 4 from by ring) rfl
            (C.negReverse).shift4).points k⁻¹).tail.dropLast).map (TsimInv k)) :=
        CycleRel.map_similar (δ := 0) hγ' (fun z => by simp [TsimInv]) hnorm hnorm'
          (CycleCongruent.cycleRel hcon)
      have hP'Ti : (((B.map (Tsim k)).reverse ++
          ((A.negReverse).points k⁻¹).reverse.tail.dropLast).map (TsimInv k)) =
          ((B ++ (A.points k).reverse.tail.dropLast).reverse).rotate
          ((A.points k).tail.dropLast).length := by
        rw [List.map_append, map_reverse_tail_dropLast,
          show ((A.negReverse).points k⁻¹).map (TsimInv k) =
            (((A.points k).map (Tsim k)).map (TsimInv k)).reverse from by
            rw [← List.map_reverse, BoundaryArc.negReverse_points hk],
          hmapT,
          show ((B.map (Tsim k)).reverse).map (TsimInv k) =
            ((B.map (Tsim k)).map (TsimInv k)).reverse from by rw [List.map_reverse],
          hmapT, List.reverse_reverse,
          show (B ++ (A.points k).reverse.tail.dropLast).reverse =
            (A.points k).tail.dropLast ++ B.reverse from by
            rw [List.reverse_append, reverse_tail_dropLast, List.reverse_reverse]]
        exact (List.rotate_append_length_eq _ _).symm
      have hQ'Ti : (((B.map (Tsim k)).reverse ++
          ((BoundaryArc.cast (show -t₀ = -(t₀ + 4) + 4 from by ring) rfl
          (C.negReverse).shift4).points k⁻¹).tail.dropLast).map (TsimInv k)) =
          ((B ++ (C.points k).tail.dropLast).reverse).rotate
          ((C.points k).reverse.tail.dropLast).length := by
        rw [List.map_append, map_tail_dropLast,
          show ((BoundaryArc.cast _ _ _).points k⁻¹).map (TsimInv k) =
            (((C.points k).map (Tsim k)).map (TsimInv k)).reverse from by
            rw [← List.map_reverse, show (BoundaryArc.cast _ _ _).points k⁻¹ =
              ((C.negReverse).shift4).points k⁻¹ from rfl, BoundaryArc.shift4_points,
              BoundaryArc.negReverse_points hk],
          hmapT,
          show ((B.map (Tsim k)).reverse).map (TsimInv k) =
            ((B.map (Tsim k)).map (TsimInv k)).reverse from by rw [List.map_reverse],
          hmapT,
          show (B ++ (C.points k).tail.dropLast).reverse =
            (C.points k).reverse.tail.dropLast ++ B.reverse from by
            rw [List.reverse_append, reverse_tail_dropLast]]
        exact (List.rotate_append_length_eq _ _).symm
      rw [hP'Ti, hQ'Ti] at hrel
      have hQne : (B ++ (C.points k).tail.dropLast).reverse ≠ [] :=
        ne_nil_of_length_pos (by rw [List.length_reverse, List.length_append]; omega)
      have hrel2 := CycleRel.rotate_left_elim hrel
      have hrel3 := CycleRel.rotate_right_elim hQne hrel2
      have hrel4 := CycleRel.reverse hrel3
      rw [List.reverse_reverse, List.reverse_reverse] at hrel4
      exact hncong (CycleRel.congruent hrel4)

snip end

/-- The answer: the dissection is possible exactly for positive `k ≠ 1`. -/
determine SolutionSet : Set ℝ := {k | 0 < k ∧ k ≠ 1}

problem usa2004_p3 (k : ℝ) (hk : 0 < k) : Dissectable k ↔ k ≠ 1 := by
  constructor
  · intro h1 h2
    rw [h2] at h1
    exact not_dissectable_one h1
  · intro h1
    rcases lt_or_gt_of_ne h1 with h2 | h2
    · have h3 : 1 < k⁻¹ := (one_lt_inv₀ hk).2 h2
      have h4 := dissectable_inverse (inv_pos.2 hk) (dissectable_gt_one (k := k⁻¹) h3)
      rwa [inv_inv] at h4
    · exact dissectable_gt_one h2

end Usa2004P3
