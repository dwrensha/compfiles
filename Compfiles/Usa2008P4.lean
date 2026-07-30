/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw, Kimi K3
-/

module

public import Mathlib.Algebra.BigOperators.Ring.List
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Ring.Basic
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics, .Geometry] }

/-!
# USA Mathematical Olympiad 2008, Problem 4

Let P be a convex polygon with n sides, n ≥ 3. Any set of n − 3 diagonals
of P that do not intersect in the interior of the polygon determine a
triangulation of P into n − 2 triangles. If P is regular and there is a
triangulation of P consisting of only isosceles triangles, find all the
possible values of n.
-/

namespace Usa2008P4

snip begin

/-!
## Chord distances in a regular n-gon

We formalize triangulations of the regular n-gon combinatorially.
The vertices are `0, 1, …, n-1` arranged on a circle, and the chord
length between two vertices is (up to the monotone factor `2R sin(π·/n)`)
determined by the circular distance `cd n i j = min (j-i) (n-(j-i))`.
A triangulation is represented by its dual binary tree: `Triang s u v`
is a triangulation of the polygonal region whose vertices are the
arithmetic progression `u, u+s, u+2s, …, v`; the `edge` constructor is a
single chord `{a, a+s}` (a side of the region) and `node` glues two
triangulations along the triangle `{a, b, c}`. The closing side of the
region (the chord `{u, v}`) is implicit at the root. Every triangulation
of a convex polygon by non-crossing diagonals arises in this way
(this is the standard Catalan correspondence), so existence of an
isosceles triangulation in the geometric sense is faithfully captured by
`Works n` below.
-/

/-- Circular distance between vertices `i` and `j` of the regular `n`-gon:
the minimum number of sides of the polygon one must traverse to get from
`i` to `j`. Two chords have equal length iff their circular distances
are equal. -/
def cd (n i j : ℕ) : ℕ := min ((i + n - j) % n) ((j + n - i) % n)

/-- A triangle with vertices `a b c` of the regular `n`-gon is isosceles:
two of its three side lengths are equal. -/
def IsoTri (n a b c : ℕ) : Prop :=
  cd n a b = cd n b c ∨ cd n b c = cd n c a ∨ cd n c a = cd n a b

lemma cd_comm (n i j : ℕ) : cd n i j = cd n j i := by
  unfold cd; rw [min_comm]

lemma cd_of_lt {n i j : ℕ} (hi : i < j) (hj : j < n) :
    cd n i j = min (j - i) (n - (j - i)) := by
  unfold cd
  have h1 : (j + n - i) % n = j - i := by
    have hji : j + n - i = (j - i) + n := by omega
    rw [hji, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  have h2 : (i + n - j) % n = n - (j - i) := by
    have hij : i + n - j = n - (j - i) := by omega
    rw [hij, Nat.mod_eq_of_lt (by omega)]
  rw [h1, h2, min_comm]

lemma min_self_sub_eq {x y n : ℕ} (hx : x ≤ n) (hy : y ≤ n)
    (h : min x (n - x) = min y (n - y)) : x = y ∨ x + y = n := by
  have g : ∀ {z : ℕ}, ¬ z ≤ n - z → n - z ≤ z := fun hz => (not_le.mp hz).le
  by_cases hx2 : x ≤ n - x <;> by_cases hy2 : y ≤ n - y
  · rw [min_eq_left hx2, min_eq_left hy2] at h; exact Or.inl h
  · rw [min_eq_left hx2, min_eq_right (g hy2)] at h
    right; omega
  · rw [min_eq_right (g hx2), min_eq_left hy2] at h
    right; omega
  · rw [min_eq_right (g hx2), min_eq_right (g hy2)] at h
    left; omega

/-- For three distinct vertices in increasing order, isoscelesness is a
purely linear condition on the gaps. -/
lemma isoTri_iff {a b c n : ℕ} (ha : a < b) (hb : b < c) (hc : c < n)
    (hn : 2 ≤ n) :
    IsoTri n a b c ↔
      b - a = c - b ∨ (c - b) + (c - a) = n ∨ (c - a) + (b - a) = n := by
  have h1 : 0 < b - a := by omega
  have h2 : 0 < c - b := by omega
  have h3 : c - a ≤ n - 1 := by omega
  have h4 : b - a ≤ n - 1 := by omega
  have h5 : c - b ≤ n - 1 := by omega
  unfold IsoTri
  rw [cd_of_lt ha (by omega), cd_of_lt hb hc, cd_comm n c a,
    cd_of_lt (by omega) hc]
  constructor
  · rintro (h | h | h)
    · obtain h' | h' := min_self_sub_eq (by omega : b - a ≤ n)
        (by omega : c - b ≤ n) h
      · exact Or.inl h'
      · exfalso; omega
    · obtain h' | h' := min_self_sub_eq (by omega : c - b ≤ n)
        (by omega : c - a ≤ n) h
      · exfalso; omega
      · exact Or.inr (Or.inl h')
    · obtain h' | h' := min_self_sub_eq (by omega : c - a ≤ n)
        (by omega : b - a ≤ n) h
      · exfalso; omega
      · exact Or.inr (Or.inr h')
  · rintro (h | h | h)
    · left
      have h6 : b - a ≤ n - (b - a) := by omega
      have h7 : c - b ≤ n - (c - b) := by omega
      rw [min_eq_left h6, min_eq_left h7, h]
    · right; left
      have e1 : n - (c - b) = c - a := by omega
      have e2 : n - (c - a) = c - b := by omega
      rw [e1, e2, min_comm]
    · right; right
      have e1 : n - (c - a) = b - a := by omega
      have e2 : n - (b - a) = c - a := by omega
      rw [e1, e2, min_comm]

/-- The triangle on side `{s, s+1}` with third vertex `x > s+1` is
isosceles only in one of three ways: an ear (`x = s+2`), a big triangle
(only for odd `n`), or the wrap-around ear (`s = 0`, `x = n-1`). -/
lemma iso_unit_right {n s x : ℕ} (hn : 3 ≤ n) (hs : s + 1 < x) (hx : x < n) :
    IsoTri n s (s + 1) x →
      x = s + 2 ∨ (Odd n ∧ 2 * x = 2 * s + 1 + n) ∨ (s = 0 ∧ x = n - 1) := by
  intro h
  have h0 : s + 1 < n := by omega
  obtain h1 | h1 | h1 := (isoTri_iff (by omega) hs hx (by omega)).mp h
  · left; omega
  · right; left
    have h2 : 2 * x = 2 * s + 1 + n := by omega
    refine ⟨?_, h2⟩
    rcases Nat.even_or_odd n with hne | hno
    · obtain ⟨k, hk⟩ := hne; exfalso; omega
    · exact hno
  · right; right; omega

/-- The triangle on side `{s, s+1}` with third vertex `x < s` is
isosceles only in one of three ways. -/
lemma iso_unit_left {n s x : ℕ} (hn : 3 ≤ n) (hs : x < s) (hx : s + 1 < n) :
    IsoTri n x s (s + 1) →
      x + 1 = s ∨ (Odd n ∧ 2 * s + 1 - 2 * x = n) ∨ (x = 0 ∧ s + 1 = n - 1) := by
  intro h
  obtain h1 | h1 | h1 := (isoTri_iff hs (by omega) hx (by omega)).mp h
  · left; omega
  · right; right; omega
  · right; left
    have h2 : 2 * s + 1 - 2 * x = n := by omega
    refine ⟨?_, h2⟩
    rcases Nat.even_or_odd n with hne | hno
    · obtain ⟨k, hk⟩ := hne; exfalso; omega
    · exact hno

/-- The triangle containing the wrap-around side `{0, n-1}` is isosceles
only in one of three ways: ear at `0` (`k = 1`), ear at `n-1`
(`k + 1 = n - 1`), or a big triangle (`2k = n-1`, only possible for odd
`n`). -/
lemma iso_wrap {n k : ℕ} (hn : 3 ≤ n) (h0 : 0 < k) (hk : k < n - 1) :
    IsoTri n 0 k (n - 1) → k = 1 ∨ k + 1 = n - 1 ∨ 2 * k = n - 1 := by
  intro h
  have h1 : n - 1 < n := by omega
  obtain h2 | h2 | h2 := (isoTri_iff h0 hk h1 (by omega)).mp h
  · right; right; omega
  · right; left; omega
  · left; omega

lemma cd_add (n i j t : ℕ) : cd n (i + t) (j + t) = cd n i j := by
  unfold cd
  have h1 : i + t + n - (j + t) = i + n - j := by omega
  have h2 : j + t + n - (i + t) = j + n - i := by omega
  rw [h1, h2]

lemma cd_one {n x : ℕ} (hn : 2 ≤ n) (hx : x + 1 < n) : cd n x (x + 1) = 1 := by
  rw [cd_of_lt (by omega) hx]
  have h1 : x + 1 - x = 1 := by omega
  rw [h1, min_eq_left (by omega)]

lemma cd_wrap {n : ℕ} (hn : 2 ≤ n) : cd n 0 (n - 1) = 1 := by
  rw [cd_of_lt (by omega) (by omega)]
  have h1 : n - 1 - 0 = n - 1 := by omega
  have h2 : n - (n - 1) = 1 := by omega
  rw [h1, h2, min_eq_right (by omega)]

/-- Doubling all vertices of a triangle in a polygon with twice as many
sides doubles the circular distance. -/
lemma cd_two_mul {m x y : ℕ} (hx : x ≤ y) (hy : y ≤ m) :
    cd (2 * m) (2 * x) (2 * y) = 2 * cd m x y := by
  by_cases hxy : x = y
  · subst hxy
    have e1 : cd (2 * m) (2 * x) (2 * x) = 0 := by
      unfold cd
      have h1 : 2 * x + 2 * m - 2 * x = 2 * m := by omega
      rw [h1, Nat.mod_self, min_self]
    have e2 : cd m x x = 0 := by
      unfold cd
      have h1 : x + m - x = m := by omega
      rw [h1, Nat.mod_self, min_self]
    rw [e1, e2, Nat.mul_zero]
  · by_cases hx0 : x = 0
    · subst hx0
      by_cases hy0 : y = 0
      · subst hy0
        have e1 : cd (2 * m) 0 0 = 0 := by
          unfold cd
          have h1 : 0 + 2 * m - 0 = 2 * m := by omega
          rw [h1, Nat.mod_self, min_self]
        have e2 : cd m 0 0 = 0 := by
          unfold cd
          have h1 : 0 + m - 0 = m := by omega
          rw [h1, Nat.mod_self, min_self]
        rw [e1, e2, Nat.mul_zero]
      · by_cases hym : y = m
        · subst y
          have e1 : cd (2 * m) 0 (2 * m) = 0 := by
            unfold cd
            have h1 : 0 + 2 * m - 2 * m = 0 := by omega
            have h2 : 2 * m + 2 * m - 0 = 2 * (2 * m) := by omega
            rw [h1, h2, Nat.zero_mod, Nat.mul_mod_left, min_self]
          have e2 : cd m 0 m = 0 := by
            unfold cd
            have h1 : 0 + m - m = 0 := by omega
            have h2 : m + m - 0 = 2 * m := by omega
            rw [h1, h2, Nat.zero_mod, Nat.mul_mod_left, min_self]
          rw [e1, e2, Nat.mul_zero]
        · have hym' : y < m := by omega
          have e1 : cd (2 * m) 0 (2 * y) = min (2 * y) (2 * m - 2 * y) := by
            unfold cd
            have h1 : 0 + 2 * m - 2 * y = 2 * m - 2 * y := by omega
            have h2 : 2 * y + 2 * m - 0 = 2 * y + 2 * m := by omega
            rw [h1, h2, Nat.add_mod_right,
              Nat.mod_eq_of_lt (by omega : 2 * y < 2 * m),
              Nat.mod_eq_of_lt (by omega : 2 * m - 2 * y < 2 * m),
              min_comm]
          have e2 : cd m 0 y = min y (m - y) := by
            rw [cd_of_lt (by omega) hym']
            have g1 : y - 0 = y := by omega
            rw [g1]
          rw [e1, e2, mul_min]
          have h6 : 2 * m - 2 * y = 2 * (m - y) := by omega
          rw [h6]
    · -- 0 < x < y ≤ m
      by_cases hym : y = m
      · have hxm : x < m := by omega
        have e1 : cd (2 * m) (2 * x) (2 * m) = min (2 * x) (2 * m - 2 * x) := by
          unfold cd
          have h1 : 2 * x + 2 * m - 2 * m = 2 * x := by omega
          have h2 : 2 * m + 2 * m - 2 * x = (2 * m - 2 * x) + 2 * m := by omega
          rw [h1, h2, Nat.add_mod_right,
            Nat.mod_eq_of_lt (by omega : 2 * x < 2 * m),
            Nat.mod_eq_of_lt (by omega : 2 * m - 2 * x < 2 * m)]
        have e2 : cd m x m = min x (m - x) := by
          unfold cd
          have h1 : x + m - m = x := by omega
          have h2 : m + m - x = (m - x) + m := by omega
          rw [h1, h2, Nat.add_mod_right,
            Nat.mod_eq_of_lt (by omega : x < m),
            Nat.mod_eq_of_lt (by omega : m - x < m)]
        rw [hym, e1, e2, mul_min]
        have h3 : 2 * m - 2 * x = 2 * (m - x) := by omega
        rw [h3]
      · have h1 : 0 < y - x := by omega
        have h2 : y < m := by omega
        rw [cd_of_lt (by omega) (by omega : 2 * y < 2 * m),
            cd_of_lt (by omega) (by omega : y < m)]
        have h3 : 2 * y - 2 * x = 2 * (y - x) := by omega
        have h4 : 2 * m - 2 * (y - x) = 2 * (m - (y - x)) := by omega
        rw [h3, h4, mul_min 2]

/-- In a polygon with `4m₂+1` sides, chords between even vertices in the
range `[0, 2m₂]` never wrap around, so the circular distance is linear. -/
lemma cd_odd_double {m₂ x y : ℕ} (hx : x ≤ y) (hy : y ≤ m₂) :
    cd (4 * m₂ + 1) (2 * x) (2 * y) = 2 * (y - x) := by
  by_cases hxy : x = y
  · subst hxy
    have e1 : cd (4 * m₂ + 1) (2 * x) (2 * x) = 0 := by
      unfold cd
      have h1 : 2 * x + (4 * m₂ + 1) - 2 * x = 4 * m₂ + 1 := by omega
      rw [h1, Nat.mod_self, min_self]
    rw [e1]
    have h2 : x - x = 0 := by omega
    rw [h2, Nat.mul_zero]
  · have h1 : 0 < y - x := by omega
    rw [cd_of_lt (by omega) (by omega : 2 * y < 4 * m₂ + 1)]
    have h2 : 2 * y - 2 * x = 2 * (y - x) := by omega
    rw [h2, min_eq_left (show 2 * (y - x) ≤ 4 * m₂ + 1 - 2 * (y - x) by omega)]


/-!
## Triangulation trees

`Triang s` : a binary tree of triangles. Together with the well-formedness
predicate `WF T u v`, such a tree represents a triangulation of the convex
polygonal region whose vertices are the arithmetic progression
`u, u+s, u+2s, …, v`: `edge a` is the trivial triangulation of a single
chord `{a, a+s}` (a side of the region), and `node a b c l r` glues two
triangulations of `[a,b]` and `[b,c]` along the triangle `{a,b,c}`. The
chord `{u,v}` closing the region is implicit at the root. Every
triangulation of a convex polygon by non-crossing diagonals arises in this
way (the standard Catalan correspondence), so existence of an isosceles
triangulation in the geometric sense is faithfully captured by `Works n`
below.
-/

inductive Triang (s : ℕ) : Type where
  | edge (a : ℕ) : Triang s
  | node (a b c : ℕ) (l r : Triang s) : Triang s

namespace Triang

/-- The triangles of a triangulation tree, as a list of triples `(a,b,c)`
with `a < b < c`. -/
def nodes {s : ℕ} : Triang s → List (ℕ × ℕ × ℕ)
  | .edge _ => []
  | .node a b c l r => (a, b, c) :: l.nodes ++ r.nodes

/-- The leaves (chords) of a triangulation tree, given by start vertex. -/
def leaves {s : ℕ} : Triang s → List ℕ
  | .edge a => [a]
  | .node _ _ _ l r => l.leaves ++ r.leaves

/-- Well-formedness: `T` is a triangulation of the region with vertices
`u, u+s, …, v`. -/
def WF {s : ℕ} : Triang s → ℕ → ℕ → Prop
  | .edge a, u, v => u = a ∧ v = a + s
  | .node a b c l r, u, v => u = a ∧ v = c ∧ WF l a b ∧ WF r b c

/-- All triangles of the triangulation are isosceles with respect to the
regular `n`-gon metric. -/
def AllIso (n : ℕ) {s : ℕ} (T : Triang s) : Prop :=
  ∀ a b c, (a, b, c) ∈ T.nodes → IsoTri n a b c

/-- All triangles have their apex at the midpoint (`b` is the midpoint of
`a` and `c`); this is what "isosceles" becomes in a linear metric. -/
def AllMid {s : ℕ} (T : Triang s) : Prop :=
  ∀ a b c, (a, b, c) ∈ T.nodes → b + b = a + c

/-- Every node of the triangulation that is adjacent to a leaf is in fact
an ear (both children are leaves). -/
def LeafEar {s : ℕ} (T : Triang s) : Prop :=
  ∀ a b c, (a, b, c) ∈ T.nodes →
    b = a + 1 ∨ c = b + 1 → b = a + 1 ∧ c = b + 1

lemma nodes_edge {s : ℕ} (a : ℕ) : (Triang.edge a : Triang s).nodes = [] := rfl

lemma nodes_node {s : ℕ} (a b c : ℕ) (l r : Triang s) :
    (Triang.node a b c l r).nodes = (a, b, c) :: l.nodes ++ r.nodes := rfl

lemma leaves_edge {s : ℕ} (a : ℕ) : (Triang.edge a : Triang s).leaves = [a] := rfl

lemma leaves_node {s : ℕ} (a b c : ℕ) (l r : Triang s) :
    (Triang.node a b c l r).leaves = l.leaves ++ r.leaves := rfl

lemma wf_edge {s a u v : ℕ} :
    WF (Triang.edge a : Triang s) u v ↔ u = a ∧ v = a + s := Iff.rfl

lemma wf_node {s a b c u v : ℕ} {l r : Triang s} :
    WF (Triang.node a b c l r) u v ↔ u = a ∧ v = c ∧ WF l a b ∧ WF r b c := Iff.rfl

lemma lt_of_wf {s : ℕ} (hs : 0 < s) {T : Triang s} {u v : ℕ} (h : WF T u v) :
    u < v := by
  induction T generalizing u v with
  | edge a => obtain ⟨rfl, rfl⟩ := h; omega
  | node a b c l r ihl ihr =>
    obtain ⟨rfl, rfl, hl, hr⟩ := h
    have h1 := ihl hl
    have h2 := ihr hr
    omega

lemma node_mem_bounds {s : ℕ} (hs : 0 < s) {T : Triang s} {u v a b c : ℕ}
    (hw : WF T u v) (h : (a, b, c) ∈ T.nodes) :
    u ≤ a ∧ a < b ∧ b < c ∧ c ≤ v := by
  induction T generalizing u v with
  | edge x => simp [nodes_edge] at h
  | node x y z l r ihl ihr =>
    obtain ⟨rfl, rfl, hl, hr⟩ := hw
    have hxy : u ≤ y := (lt_of_wf hs hl).le
    have hyz : y ≤ v := (lt_of_wf hs hr).le
    rw [nodes_node] at h
    simp only [List.mem_cons, List.mem_append] at h
    rcases h with (h | h) | h
    · simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2, h3⟩ := h
      subst h1; subst h2; subst h3
      exact ⟨le_refl _, lt_of_wf hs hl, lt_of_wf hs hr, le_refl _⟩
    · obtain ⟨h1, h2, h3, h4⟩ := ihl hl h
      exact ⟨h1, h2, h3, by omega⟩
    · obtain ⟨h1, h2, h3, h4⟩ := ihr hr h
      exact ⟨by omega, h2, h3, h4⟩

lemma dvd_span {s : ℕ} (hs : 0 < s) {T : Triang s} {u v : ℕ} (hw : WF T u v) :
    s ∣ v - u := by
  induction T generalizing u v with
  | edge a => obtain ⟨rfl, rfl⟩ := hw; exact ⟨1, by omega⟩
  | node x y z l r ihl ihr =>
    obtain ⟨rfl, rfl, hl, hr⟩ := hw
    have hxy : u ≤ y := (lt_of_wf hs hl).le
    have hyz : y ≤ v := (lt_of_wf hs hr).le
    obtain ⟨i, hi⟩ := ihl hl
    obtain ⟨j, hj⟩ := ihr hr
    exact ⟨i + j, by rw [Nat.mul_add]; omega⟩

lemma node_mem_dvd {s : ℕ} (hs : 0 < s) {T : Triang s} {u v a b c : ℕ}
    (hw : WF T u v) (h : (a, b, c) ∈ T.nodes) :
    s ∣ a - u ∧ s ∣ b - u ∧ s ∣ c - u := by
  induction T generalizing u v with
  | edge x => simp [nodes_edge] at h
  | node x y z l r ihl ihr =>
    obtain ⟨rfl, rfl, hl, hr⟩ := hw
    rw [nodes_node] at h
    simp only [List.mem_cons, List.mem_append] at h
    rcases h with (h | h) | h
    · simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2, h3⟩ := h
      subst h1; subst h2; subst h3
      refine ⟨⟨0, by omega⟩, dvd_span hs hl, ?_⟩
      have hxy : a ≤ b := (lt_of_wf hs hl).le
      have hyz : b ≤ c := (lt_of_wf hs hr).le
      obtain ⟨i, hi⟩ := dvd_span hs hl
      obtain ⟨j, hj⟩ := dvd_span hs hr
      exact ⟨i + j, by rw [Nat.mul_add]; omega⟩
    · exact ihl hl h
    · obtain ⟨h1, h2, h3⟩ := ihr hr h
      obtain ⟨hya, hab, hbc, -⟩ := node_mem_bounds hs hr h
      obtain ⟨j, hj⟩ := dvd_span hs hl
      obtain ⟨i1, hi1⟩ := h1
      obtain ⟨i2, hi2⟩ := h2
      obtain ⟨i3, hi3⟩ := h3
      have hxy : u ≤ y := (lt_of_wf hs hl).le
      exact ⟨⟨i1 + j, by rw [Nat.mul_add]; omega⟩,
        ⟨i2 + j, by rw [Nat.mul_add]; omega⟩,
        ⟨i3 + j, by rw [Nat.mul_add]; omega⟩⟩

lemma leaf_mem_bounds {s : ℕ} (hs : 0 < s) {T : Triang s} {u v a : ℕ}
    (hw : WF T u v) (h : a ∈ T.leaves) : u ≤ a ∧ a + s ≤ v := by
  induction T generalizing u v with
  | edge x =>
    obtain ⟨rfl, rfl⟩ := hw
    rw [leaves_edge] at h
    simp at h
    obtain rfl := h
    exact ⟨le_refl _, le_refl _⟩
  | node x y z l r ihl ihr =>
    obtain ⟨rfl, rfl, hl, hr⟩ := hw
    have hxy : u ≤ y := (lt_of_wf hs hl).le
    have hyz : y ≤ v := (lt_of_wf hs hr).le
    rw [leaves_node] at h
    simp at h
    rcases h with h | h
    · obtain ⟨h1, h2⟩ := ihl hl h
      exact ⟨h1, by omega⟩
    · obtain ⟨h1, h2⟩ := ihr hr h
      exact ⟨by omega, h2⟩

/-- The root triangle of a node is a member of its triangle list. -/
lemma mem_nodes_root {s : ℕ} (a b c : ℕ) (l r : Triang s) :
    (a, b, c) ∈ (Triang.node a b c l r).nodes := by
  rw [nodes_node]
  exact List.mem_cons_self ..

lemma mem_nodes_left {s a b c d e f : ℕ} {l r : Triang s}
    (h : (a, b, c) ∈ l.nodes) : (a, b, c) ∈ (Triang.node d e f l r).nodes :=
  List.mem_cons_of_mem _ (List.mem_append_left _ h)

lemma mem_nodes_right {s a b c d e f : ℕ} {l r : Triang s}
    (h : (a, b, c) ∈ r.nodes) : (a, b, c) ∈ (Triang.node d e f l r).nodes :=
  List.mem_cons_of_mem _ (List.mem_append_right _ h)

lemma leafEar_left {a b c : ℕ} {l r : Triang 1}
    (h : (Triang.node a b c l r).LeafEar) : l.LeafEar := by
  intro x y z hmem hh
  exact h x y z (mem_nodes_left hmem) hh

lemma leafEar_right {a b c : ℕ} {l r : Triang 1}
    (h : (Triang.node a b c l r).LeafEar) : r.LeafEar := by
  intro x y z hmem hh
  exact h x y z (mem_nodes_right hmem) hh

lemma allIso_left {s n a b c : ℕ} {l r : Triang s}
    (h : (Triang.node a b c l r).AllIso n) : l.AllIso n := by
  intro x y z hmem
  exact h x y z (mem_nodes_left hmem)

lemma allIso_right {s n a b c : ℕ} {l r : Triang s}
    (h : (Triang.node a b c l r).AllIso n) : r.AllIso n := by
  intro x y z hmem
  exact h x y z (mem_nodes_right hmem)

lemma allMid_left {s a b c : ℕ} {l r : Triang s}
    (h : (Triang.node a b c l r).AllMid) : l.AllMid := by
  intro x y z hmem
  exact h x y z (mem_nodes_left hmem)

lemma allMid_right {s a b c : ℕ} {l r : Triang s}
    (h : (Triang.node a b c l r).AllMid) : r.AllMid := by
  intro x y z hmem
  exact h x y z (mem_nodes_right hmem)

end Triang

/-!
## Tree operations

Translations, rescaling by a factor of two (in both directions), and ear
insertion, together with their effect on well-formedness and on the
isosceles/midpoint predicates.
-/

namespace Triang

/-- Translate all vertices by `t`. -/
def translateTree (t : ℕ) {s : ℕ} : Triang s → Triang s
  | .edge a => .edge (a + t)
  | .node a b c l r => .node (a + t) (b + t) (c + t) (translateTree t l) (translateTree t r)

lemma nodes_translate (t : ℕ) {s : ℕ} (T : Triang s) :
    (translateTree t T).nodes =
      T.nodes.map (fun p ↦ (p.1 + t, p.2.1 + t, p.2.2 + t)) := by
  induction T with
  | edge a => rfl
  | node a b c l r ihl ihr => simp [translateTree, nodes, ihl, ihr]

lemma wf_translate (t : ℕ) {s : ℕ} {T : Triang s} {u v : ℕ} (hw : WF T u v) :
    WF (translateTree t T) (u + t) (v + t) := by
  induction T generalizing u v with
  | edge a => obtain ⟨rfl, rfl⟩ := hw; exact ⟨rfl, by omega⟩
  | node a b c l r ihl ihr =>
    obtain ⟨rfl, rfl, hl, hr⟩ := hw
    exact ⟨rfl, rfl, ihl hl, ihr hr⟩

/-- Double all vertices: step `s` becomes step `2s`. -/
def doubleTree {s : ℕ} : Triang s → Triang (2 * s)
  | .edge a => .edge (2 * a)
  | .node a b c l r => .node (2 * a) (2 * b) (2 * c) (doubleTree l) (doubleTree r)

lemma nodes_double {s : ℕ} (T : Triang s) :
    (doubleTree T).nodes =
      T.nodes.map (fun p ↦ (2 * p.1, 2 * p.2.1, 2 * p.2.2)) := by
  induction T with
  | edge a => rfl
  | node a b c l r ihl ihr => simp [doubleTree, nodes, ihl, ihr]

lemma wf_double {s : ℕ} {T : Triang s} {u v : ℕ} (hw : WF T u v) :
    WF (doubleTree T) (2 * u) (2 * v) := by
  induction T generalizing u v with
  | edge a => obtain ⟨rfl, rfl⟩ := hw; exact ⟨rfl, by omega⟩
  | node a b c l r ihl ihr =>
    obtain ⟨rfl, rfl, hl, hr⟩ := hw
    exact ⟨rfl, rfl, ihl hl, ihr hr⟩

/-- Halve all vertices: step `2s` becomes step `s`. -/
def halveTree : Triang 2 → Triang 1
  | .edge a => .edge (a / 2)
  | .node a b c l r => .node (a / 2) (b / 2) (c / 2) (halveTree l) (halveTree r)

lemma nodes_halve (T : Triang 2) :
    (halveTree T).nodes =
      T.nodes.map (fun p ↦ (p.1 / 2, p.2.1 / 2, p.2.2 / 2)) := by
  induction T with
  | edge a => rfl
  | node a b c l r ihl ihr => simp [halveTree, nodes, ihl, ihr]

lemma wf_halve {T : Triang 2} {u v : ℕ} (hw : WF T u v) :
    WF (halveTree T) (u / 2) (v / 2) := by
  induction T generalizing u v with
  | edge a => obtain ⟨rfl, rfl⟩ := hw; exact ⟨rfl, by omega⟩
  | node a b c l r ihl ihr =>
    obtain ⟨rfl, rfl, hl, hr⟩ := hw
    exact ⟨rfl, rfl, ihl hl, ihr hr⟩

/-- Insert an ear on every chord of a step-2 triangulation:
the leaf `{a, a+2}` becomes the ear `{a, a+1, a+2}`. -/
def inflate : Triang 2 → Triang 1
  | .edge a => .node a (a + 1) (a + 2) (.edge a) (.edge (a + 1))
  | .node a b c l r => .node a b c (inflate l) (inflate r)

lemma wf_inflate {T : Triang 2} {u v : ℕ} (hw : WF T u v) :
    WF (inflate T) u v := by
  induction T generalizing u v with
  | edge a => obtain ⟨rfl, rfl⟩ := hw; exact ⟨rfl, rfl, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩
  | node a b c l r ihl ihr =>
    obtain ⟨rfl, rfl, hl, hr⟩ := hw
    exact ⟨rfl, rfl, ihl hl, ihr hr⟩

lemma mem_nodes_inflate {T : Triang 2} {t : ℕ × ℕ × ℕ}
    (h : t ∈ (inflate T).nodes) :
    t ∈ T.nodes ∨ ∃ a ∈ T.leaves, t = (a, a + 1, a + 2) := by
  induction T with
  | edge a =>
    rw [inflate, nodes_node] at h
    rcases List.mem_cons.mp h with h | h
    · right
      exact ⟨a, by rw [leaves_edge]; simp, h⟩
    · simp [nodes_edge] at h
  | node a b c l r ihl ihr =>
    rw [inflate, nodes_node] at h
    rcases List.mem_cons.mp h with h | h
    · subst h
      left
      exact mem_nodes_root a b c l r
    · rcases List.mem_append.mp h with h | h
      · obtain h' | h' := ihl h
        · left; exact mem_nodes_left h'
        · right
          obtain ⟨x, hxl, hx⟩ := h'
          exact ⟨x, by rw [leaves_node]; exact List.mem_append_left _ hxl, hx⟩
      · obtain h' | h' := ihr h
        · left; exact mem_nodes_right h'
        · right
          obtain ⟨x, hxl, hx⟩ := h'
          exact ⟨x, by rw [leaves_node]; exact List.mem_append_right _ hxl, hx⟩

end Triang

/-!
## Transfer of isoscelesness along the tree operations
-/

lemma isoTri_add {n a b c : ℕ} (t : ℕ) :
    IsoTri n (a + t) (b + t) (c + t) ↔ IsoTri n a b c := by
  unfold IsoTri
  rw [cd_add n a b t, cd_add n b c t, cd_add n c a t]

lemma iso_ear {n a : ℕ} (ha : a + 2 < n) : IsoTri n a (a + 1) (a + 2) := by
  left
  rw [cd_one (by omega) (by omega), cd_one (by omega) ha]

namespace Triang

lemma allIso_translate {n : ℕ} {s : ℕ} {T : Triang s} (t : ℕ) (h : AllIso n T) :
    AllIso n (translateTree t T) := by
  intro a b c hc
  rw [nodes_translate] at hc
  obtain ⟨⟨a', b', c'⟩, hp, hft⟩ := List.mem_map.mp hc
  have e1 : a = a' + t := (congrArg Prod.fst hft).symm
  have e2 : b = b' + t := (congrArg (fun p ↦ p.2.1) hft).symm
  have e3 : c = c' + t := (congrArg (fun p ↦ p.2.2) hft).symm
  subst e1; subst e2; subst e3
  rw [isoTri_add t]
  exact h a' b' c' hp

lemma allMid_translate {s : ℕ} {T : Triang s} (t : ℕ) (h : AllMid T) :
    AllMid (translateTree t T) := by
  intro a b c hc
  rw [nodes_translate] at hc
  obtain ⟨⟨a', b', c'⟩, hp, hft⟩ := List.mem_map.mp hc
  have e1 : a = a' + t := (congrArg Prod.fst hft).symm
  have e2 : b = b' + t := (congrArg (fun p ↦ p.2.1) hft).symm
  have e3 : c = c' + t := (congrArg (fun p ↦ p.2.2) hft).symm
  subst e1; subst e2; subst e3
  have := h a' b' c' hp
  omega

lemma allIso_double {n s : ℕ} (hs : 0 < s) {T : Triang s} {u v : ℕ}
    (hw : WF T u v) (hv : v ≤ n) (h : AllIso n T) : AllIso (2 * n) (doubleTree T) := by
  intro a b c hc
  rw [nodes_double] at hc
  obtain ⟨⟨a', b', c'⟩, hp, hft⟩ := List.mem_map.mp hc
  have e1 : a = 2 * a' := (congrArg Prod.fst hft).symm
  have e2 : b = 2 * b' := (congrArg (fun p ↦ p.2.1) hft).symm
  have e3 : c = 2 * c' := (congrArg (fun p ↦ p.2.2) hft).symm
  subst e1; subst e2; subst e3
  obtain ⟨-, hab, hbc, hcv⟩ := node_mem_bounds hs hw hp
  have h' := h a' b' c' hp
  unfold IsoTri at h' ⊢
  rw [cd_two_mul (by omega : a' ≤ b') (by omega : b' ≤ n),
    cd_two_mul (by omega : b' ≤ c') (by omega : c' ≤ n),
    cd_comm (2 * n) (2 * c') (2 * a'),
    cd_two_mul (by omega : a' ≤ c') (by omega : c' ≤ n)]
  rw [cd_comm n c' a'] at h'
  omega

/-- Halving an isosceles triangulation in a `2m`-gon gives an isosceles
triangulation in an `m`-gon. -/
lemma allIso_halve_even {T : Triang 2} {u v m : ℕ} (hw : WF T u v)
    (hv : v ≤ 2 * m) (h : AllIso (2 * m) T) : AllIso m (halveTree T) := by
  intro a b c hc
  rw [nodes_halve] at hc
  obtain ⟨⟨a', b', c'⟩, hp, hft⟩ := List.mem_map.mp hc
  have e1 : a = a' / 2 := (congrArg Prod.fst hft).symm
  have e2 : b = b' / 2 := (congrArg (fun p ↦ p.2.1) hft).symm
  have e3 : c = c' / 2 := (congrArg (fun p ↦ p.2.2) hft).symm
  subst e1; subst e2; subst e3
  obtain ⟨hd1, hd2, hd3⟩ := node_mem_dvd (by omega : (0:ℕ) < 2) hw hp
  obtain ⟨hu', hab, hbc, hcv⟩ := node_mem_bounds (by omega : (0:ℕ) < 2) hw hp
  obtain ⟨ka, hka⟩ := hd1
  obtain ⟨kb, hkb⟩ := hd2
  obtain ⟨kc, hkc⟩ := hd3
  have ea : a' = u + 2 * ka := by omega
  have eb : b' = u + 2 * kb := by omega
  have ec : c' = u + 2 * kc := by omega
  have e1 : cd (2 * m) a' b' = 2 * cd m ka kb := by
    rw [ea, eb, show u + 2 * ka = 2 * ka + u from by omega,
      show u + 2 * kb = 2 * kb + u from by omega, cd_add,
      cd_two_mul (by omega : ka ≤ kb) (by omega : kb ≤ m)]
  have e2 : cd (2 * m) b' c' = 2 * cd m kb kc := by
    rw [eb, ec, show u + 2 * kb = 2 * kb + u from by omega,
      show u + 2 * kc = 2 * kc + u from by omega, cd_add,
      cd_two_mul (by omega : kb ≤ kc) (by omega : kc ≤ m)]
  have e3 : cd (2 * m) c' a' = 2 * cd m kc ka := by
    rw [cd_comm, ec, ea, show u + 2 * ka = 2 * ka + u from by omega,
      show u + 2 * kc = 2 * kc + u from by omega, cd_add,
      cd_two_mul (by omega : ka ≤ kc) (by omega : kc ≤ m), cd_comm m kc ka]
  have g1 : a' / 2 = ka + u / 2 := by omega
  have g2 : b' / 2 = kb + u / 2 := by omega
  have g3 : c' / 2 = kc + u / 2 := by omega
  rw [g1, g2, g3, isoTri_add (u / 2)]
  have h' := h a' b' c' hp
  unfold IsoTri at h' ⊢
  rw [e1, e2, e3] at h'
  omega

/-- Halving an isosceles triangulation in a `(4m₂+1)`-gon gives a
midpoint triangulation (the linear metric). -/
lemma allMid_halve_odd {T : Triang 2} {u v m₂ : ℕ} (hw : WF T u v)
    (huv : v ≤ u + 2 * m₂) (h : AllIso (4 * m₂ + 1) T) : AllMid (halveTree T) := by
  intro a b c hc
  rw [nodes_halve] at hc
  obtain ⟨⟨a', b', c'⟩, hp, hft⟩ := List.mem_map.mp hc
  have e1 : a = a' / 2 := (congrArg Prod.fst hft).symm
  have e2 : b = b' / 2 := (congrArg (fun p ↦ p.2.1) hft).symm
  have e3 : c = c' / 2 := (congrArg (fun p ↦ p.2.2) hft).symm
  subst e1; subst e2; subst e3
  obtain ⟨hd1, hd2, hd3⟩ := node_mem_dvd (by omega : (0:ℕ) < 2) hw hp
  obtain ⟨hu', hab, hbc, hcv⟩ := node_mem_bounds (by omega : (0:ℕ) < 2) hw hp
  obtain ⟨ka, hka⟩ := hd1
  obtain ⟨kb, hkb⟩ := hd2
  obtain ⟨kc, hkc⟩ := hd3
  have ea : a' = u + 2 * ka := by omega
  have eb : b' = u + 2 * kb := by omega
  have ec : c' = u + 2 * kc := by omega
  have e1 : cd (4 * m₂ + 1) a' b' = 2 * (kb - ka) := by
    rw [ea, eb, show u + 2 * ka = 2 * ka + u from by omega,
      show u + 2 * kb = 2 * kb + u from by omega, cd_add,
      cd_odd_double (by omega : ka ≤ kb) (by omega : kb ≤ m₂)]
  have e2 : cd (4 * m₂ + 1) b' c' = 2 * (kc - kb) := by
    rw [eb, ec, show u + 2 * kb = 2 * kb + u from by omega,
      show u + 2 * kc = 2 * kc + u from by omega, cd_add,
      cd_odd_double (by omega : kb ≤ kc) (by omega : kc ≤ m₂)]
  have e3 : cd (4 * m₂ + 1) c' a' = 2 * (kc - ka) := by
    rw [cd_comm, ec, ea, show u + 2 * ka = 2 * ka + u from by omega,
      show u + 2 * kc = 2 * kc + u from by omega, cd_add,
      cd_odd_double (by omega : ka ≤ kc) (by omega : kc ≤ m₂)]
  have g1 : a' / 2 = u / 2 + ka := by omega
  have g2 : b' / 2 = u / 2 + kb := by omega
  have g3 : c' / 2 = u / 2 + kc := by omega
  rw [g1, g2, g3]
  have h' := h a' b' c' hp
  unfold IsoTri at h'
  rw [e1, e2, e3] at h'
  omega

lemma allIso_inflate {n : ℕ} {T : Triang 2} {u v : ℕ} (hw : WF T u v)
    (hv : v ≤ n - 1) (hn : 2 ≤ n) (h : AllIso n T) : AllIso n (inflate T) := by
  intro a b c hc
  obtain h' | ⟨x, hxl, hx⟩ := mem_nodes_inflate hc
  · exact h a b c h'
  · simp only [Prod.mk.injEq] at hx
    obtain ⟨h1, h2, h3⟩ := hx
    subst h1; subst h2; subst h3
    obtain ⟨hxu, hxv⟩ := leaf_mem_bounds (by omega : (0:ℕ) < 2) hw hxl
    exact iso_ear (by omega)

/-- A midpoint triangulation in the linear metric, doubled, is isosceles in
the `(4m₂+1)`-gon. -/
lemma allIso_double_odd {T : Triang 1} {u v m₂ : ℕ} (hw : WF T u v)
    (hv : v ≤ m₂) (h : AllMid T) : AllIso (4 * m₂ + 1) (doubleTree T) := by
  intro a b c hc
  rw [nodes_double] at hc
  obtain ⟨⟨a', b', c'⟩, hp, hft⟩ := List.mem_map.mp hc
  have e1 : a = 2 * a' := (congrArg Prod.fst hft).symm
  have e2 : b = 2 * b' := (congrArg (fun p ↦ p.2.1) hft).symm
  have e3 : c = 2 * c' := (congrArg (fun p ↦ p.2.2) hft).symm
  subst e1; subst e2; subst e3
  obtain ⟨-, hab, hbc, hcv⟩ := node_mem_bounds (by omega : (0:ℕ) < 1) hw hp
  have h' := h a' b' c' hp
  unfold IsoTri
  rw [cd_odd_double (by omega : a' ≤ b') (by omega : b' ≤ m₂),
    cd_odd_double (by omega : b' ≤ c') (by omega : c' ≤ m₂),
    cd_comm (4 * m₂ + 1) (2 * c') (2 * a'),
    cd_odd_double (by omega : a' ≤ c') (by omega : c' ≤ m₂)]
  omega

end Triang

/-!
## Ear contraction

If every leaf-adjacent node of a step-1 triangulation is an ear, then the
ears can be contracted to chords, yielding a step-2 triangulation whose
triangles are a subset of the original ones.
-/

namespace Triang

theorem subset_node {s₁ s₂ : ℕ} {a b c : ℕ} {l₁ r₁ : Triang s₁} {l₂ r₂ : Triang s₂}
    (h1 : l₁.nodes ⊆ l₂.nodes) (h2 : r₁.nodes ⊆ r₂.nodes) :
    (Triang.node a b c l₁ r₁).nodes ⊆ (Triang.node a b c l₂ r₂).nodes := by
  intro t ht
  rw [nodes_node] at ht ⊢
  rcases List.mem_cons.mp ht with h | ht
  · subst h; exact List.mem_cons_self ..
  · rcases List.mem_append.mp ht with ht | ht
    · exact List.mem_cons_of_mem _ (List.mem_append_left _ (h1 ht))
    · exact List.mem_cons_of_mem _ (List.mem_append_right _ (h2 ht))

theorem contract {u v : ℕ} {T : Triang 1} (hw : WF T u v) (hle : T.LeafEar)
    (hv : u + 2 ≤ v) : ∃ T' : Triang 2, WF T' u v ∧ T'.nodes ⊆ T.nodes := by
  induction T generalizing u v with
  | edge a => obtain ⟨rfl, rfl⟩ := hw; omega
  | node a b c l r ihl ihr =>
    obtain ⟨rfl, rfl, hl, hr⟩ := hw
    cases l with
    | edge p =>
      obtain ⟨rfl, rfl⟩ := hl
      have hroot := hle u (u + 1) v (mem_nodes_root u (u + 1) v (.edge u) r) (Or.inl rfl)
      obtain ⟨-, hvv⟩ := hroot
      have hv2 : v = u + 2 := by omega
      subst hv2
      exact ⟨Triang.edge u, ⟨rfl, rfl⟩, by intro t ht; simp [nodes_edge] at ht⟩
    | node a₁ b₁ c₁ l₁ r₁ =>
      obtain ⟨rfl, rfl, hl1, hr1⟩ := hl
      have hlt : u + 2 ≤ b := by
        have h1 := lt_of_wf (by omega : (0:ℕ) < 1) hl1
        have h2 := lt_of_wf (by omega : (0:ℕ) < 1) hr1
        omega
      cases r with
      | edge q =>
        obtain ⟨rfl, rfl⟩ := hr
        have hroot := hle u b (b + 1)
          (mem_nodes_root u b (b + 1) (.node u b₁ b l₁ r₁) (.edge b)) (Or.inr rfl)
        obtain ⟨hyy, -⟩ := hroot
        omega
      | node a₂ b₂ c₂ l₂ r₂ =>
        obtain ⟨rfl, rfl, hl2, hr2⟩ := hr
        have hlt2 : b + 2 ≤ v := by
          have h1 := lt_of_wf (by omega : (0:ℕ) < 1) hl2
          have h2 := lt_of_wf (by omega : (0:ℕ) < 1) hr2
          omega
        obtain ⟨T₁, hw1, hs1⟩ := ihl ⟨rfl, rfl, hl1, hr1⟩ (leafEar_left hle) hlt
        obtain ⟨T₂, hw2, hs2⟩ := ihr ⟨rfl, rfl, hl2, hr2⟩ (leafEar_right hle) hlt2
        refine ⟨Triang.node u b v T₁ T₂, ⟨rfl, rfl, hw1, hw2⟩, ?_⟩
        exact subset_node hs1 hs2

end Triang

/-!
## Region analysis: forced ears and contraction
-/

namespace Triang

/-- Odd region: a step-1 triangulation of `[u, u+m]` (with `2 ≤ m` and
`u + m ≤ 2m`, i.e. inside the `(2m+1)`-gon) all of whose triangles are
isosceles contracts to a step-2 triangulation; in particular `m` is even. -/
theorem regionOdd_contract {m u : ℕ} (hm : 2 ≤ m) (hu : u + m ≤ 2 * m) {T : Triang 1}
    (hw : WF T u (u + m)) (hiso : AllIso (2 * m + 1) T) :
    2 ∣ m ∧ ∃ T' : Triang 2, WF T' u (u + m) ∧
      AllIso (2 * m + 1) T' ∧ T'.nodes ⊆ T.nodes := by
  have hle : T.LeafEar := by
    intro a b c hmem hside
    obtain ⟨ha, hab, hbc, hc⟩ := node_mem_bounds (by omega : (0:ℕ) < 1) hw hmem
    have hiso' := hiso a b c hmem
    have hn : 3 ≤ 2 * m + 1 := by omega
    rcases hside with hside | hside
    · subst hside
      obtain h1 | ⟨-, h2⟩ | ⟨h3, h4⟩ :=
        iso_unit_right hn (by omega : a + 1 < c) (by omega : c < 2 * m + 1) hiso'
      · omega
      · omega
      · omega
    · subst hside
      obtain h1 | ⟨-, h2⟩ | ⟨h3, h4⟩ :=
        iso_unit_left hn (by omega : a < b) (by omega : b + 1 < 2 * m + 1) hiso'
      · omega
      · omega
      · omega
  obtain ⟨T', hw', hsub⟩ := contract hw hle (by omega)
  refine ⟨?_, T', hw', fun a b c hmem => hiso a b c (hsub hmem), hsub⟩
  have hd := dvd_span (by omega : (0:ℕ) < 2) hw'
  omega

/-- Even region: a step-1 triangulation of `[u, u + (2m−2)]` (with `3 ≤ m`
and `u + (2m−2) ≤ 2m−1`) all of whose triangles are isosceles in the
`2m`-gon contracts to a step-2 triangulation. -/
theorem regionEven_contract {m u : ℕ} (hm : 3 ≤ m) (hu : u + (2 * m - 2) ≤ 2 * m - 1)
    {T : Triang 1} (hw : WF T u (u + (2 * m - 2))) (hiso : AllIso (2 * m) T) :
    ∃ T' : Triang 2, WF T' u (u + (2 * m - 2)) ∧
      AllIso (2 * m) T' ∧ T'.nodes ⊆ T.nodes := by
  have hle : T.LeafEar := by
    intro a b c hmem hside
    obtain ⟨ha, hab, hbc, hc⟩ := node_mem_bounds (by omega : (0:ℕ) < 1) hw hmem
    have hiso' := hiso a b c hmem
    have hn : 3 ≤ 2 * m := by omega
    rcases hside with hside | hside
    · subst hside
      obtain h1 | ⟨ho, h2⟩ | ⟨h3, h4⟩ :=
        iso_unit_right hn (by omega : a + 1 < c) (by omega : c < 2 * m) hiso'
      · omega
      · obtain ⟨k, hk⟩ := ho; omega
      · omega
    · subst hside
      obtain h1 | ⟨ho, h2⟩ | ⟨h3, h4⟩ :=
        iso_unit_left hn (by omega : a < b) (by omega : b + 1 < 2 * m) hiso'
      · omega
      · obtain ⟨k, hk⟩ := ho; omega
      · omega
  obtain ⟨T', hw', hsub⟩ := contract hw hle (by omega)
  exact ⟨T', hw', fun a b c hmem => hiso a b c (hsub hmem), hsub⟩

/-- A midpoint triangulation of `[u, v]` exists only when `v - u` is a
power of two. -/
theorem allMid_pow2 {T : Triang 1} {u v : ℕ} (hw : WF T u v) (h : T.AllMid) :
    ∃ k, v - u = 2 ^ k := by
  induction T generalizing u v with
  | edge a => obtain ⟨rfl, rfl⟩ := hw; exact ⟨0, by omega⟩
  | node a b c l r ihl ihr =>
    obtain ⟨rfl, rfl, hl, hr⟩ := hw
    have hmid := h u b v (mem_nodes_root u b v l r)
    obtain ⟨k, hk⟩ := ihl hl (allMid_left h)
    have hab : u ≤ b := (lt_of_wf (by omega : (0:ℕ) < 1) hl).le
    have hbc : b ≤ v := (lt_of_wf (by omega : (0:ℕ) < 1) hr).le
    refine ⟨k + 1, ?_⟩
    have hcc : v - u = 2 * (b - u) := by omega
    rw [hcc, hk, pow_succ]
    omega

end Triang


/-!
## Counting sides in a triangulation of the full polygon
-/

namespace Triang

/-- The number of unit sides of the polygon among the sides `{a,b}` and
`{b,c}` of a triangle. (The third side `{a,c}` is never a unit edge.) -/
def unitCnt (t : ℕ × ℕ × ℕ) : ℕ :=
  (if t.2.1 = t.1 + 1 then 1 else 0) + (if t.2.2 = t.2.1 + 1 then 1 else 0)

/-- The number of times the wrap-around side `{0, n-1}` appears as a side
of a triangle. -/
def wrapCnt (n : ℕ) (t : ℕ × ℕ × ℕ) : ℕ :=
  if t.1 = 0 ∧ t.2.2 = n - 1 then 1 else 0

lemma sum_unitCnt {T : Triang 1} {u v : ℕ} (hw : WF T u v) :
    (T.nodes.map unitCnt).sum = v - u - (if v = u + 1 then 1 else 0) := by
  induction T generalizing u v with
  | edge a =>
    obtain ⟨rfl, rfl⟩ := hw
    simp [nodes_edge]
  | node a b c l r ihl ihr =>
    obtain ⟨rfl, rfl, hl, hr⟩ := hw
    have hlt : u + 2 ≤ v := by
      have h1 := lt_of_wf (by omega : (0:ℕ) < 1) hl
      have h2 := lt_of_wf (by omega : (0:ℕ) < 1) hr
      omega
    have hub : u ≤ b := (lt_of_wf (by omega : (0:ℕ) < 1) hl).le
    have hbv : b ≤ v := (lt_of_wf (by omega : (0:ℕ) < 1) hr).le
    simp only [nodes_node, List.map_cons, List.map_append, List.sum_cons, List.sum_append]
    rw [ihl hl, ihr hr]
    unfold unitCnt
    dsimp only
    split_ifs with h2 h3 h4 <;> omega

lemma sum_wrapCnt_eq_zero {T : Triang 1} {u v n : ℕ} (_hw : WF T u v)
    (hne : ∀ a b c, (a, b, c) ∈ T.nodes → ¬ (a = 0 ∧ c = n - 1)) :
    (T.nodes.map (wrapCnt n)).sum = 0 := by
  rw [List.sum_eq_zero_iff]
  intro x hx
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
  obtain ⟨a, b, c⟩ := t
  have h1 := hne a b c ht
  simp [wrapCnt, h1]

lemma sum_map_add {α : Type*} (l : List α) (f g : α → ℕ) :
    (l.map (fun t ↦ f t + g t)).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => simp
  | cons x xs ih => simp [List.map_cons, List.sum_cons, ih]; omega

lemma sum_sideCnt {T : Triang 1} {n : ℕ} (hn : 3 ≤ n) (hw : WF T 0 (n - 1)) :
    (T.nodes.map (fun t ↦ unitCnt t + wrapCnt n t)).sum = n := by
  cases T with
  | edge a =>
    obtain ⟨h1, h2⟩ := hw
    omega
  | node a b c l r =>
    obtain ⟨rfl, rfl, hl, hr⟩ := hw
    have hbl : b < n - 1 := by
      have hbc := lt_of_wf (by omega : (0:ℕ) < 1) hr
      omega
    have hb0 : 0 < b := by
      have hab := lt_of_wf (by omega : (0:ℕ) < 1) hl
      omega
    have hsuml := sum_unitCnt hl
    have hsumr := sum_unitCnt hr
    have hz_l : (l.nodes.map (wrapCnt n)).sum = 0 := by
      apply sum_wrapCnt_eq_zero hl
      intro a' b' c' hmem hcon
      obtain ⟨h1, h2, h3, h4⟩ := node_mem_bounds (by omega : (0:ℕ) < 1) hl hmem
      obtain ⟨-, hc'⟩ := hcon
      omega
    have hz_r : (r.nodes.map (wrapCnt n)).sum = 0 := by
      apply sum_wrapCnt_eq_zero hr
      intro a' b' c' hmem hcon
      obtain ⟨h1, h2, h3, h4⟩ := node_mem_bounds (by omega : (0:ℕ) < 1) hr hmem
      obtain ⟨ha', -⟩ := hcon
      omega
    rw [sum_map_add, nodes_node]
    simp only [List.map_cons, List.map_append, List.sum_cons, List.sum_append]
    rw [hsuml, hsumr, hz_l, hz_r]
    unfold unitCnt wrapCnt
    dsimp only
    split_ifs with h2 h3 h4 <;> omega

lemma exists_sideCnt_one {T : Triang 1} {n : ℕ} (hn : 5 ≤ n) (hnodd : Odd n)
    (hw : WF T 0 (n - 1)) :
    ∃ a b c, (a, b, c) ∈ T.nodes ∧ unitCnt (a, b, c) + wrapCnt n (a, b, c) = 1 := by
  have hsum := sum_sideCnt (by omega : 3 ≤ n) hw
  by_contra hcon
  push Not at hcon
  have hev : ∀ x ∈ T.nodes.map (fun t ↦ unitCnt t + wrapCnt n t), 2 ∣ x := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
    obtain ⟨a, b, c⟩ := t
    have h3 : unitCnt (a, b, c) + wrapCnt n (a, b, c) ≠ 1 := hcon a b c ht
    have h4 : unitCnt (a, b, c) + wrapCnt n (a, b, c) ≤ 2 := by
      unfold unitCnt wrapCnt
      dsimp only
      split_ifs with hc1 hc2 hc3 <;> omega
    omega
  have hev2 : 2 ∣ (T.nodes.map (fun t ↦ unitCnt t + wrapCnt n t)).sum :=
    List.dvd_sum hev
  rw [hsum] at hev2
  obtain ⟨k, hk⟩ := hev2
  obtain ⟨k', hk'⟩ := hnodd
  omega

/-- Extract the two subtrees hanging below a given triangle. -/
lemma extract_at_node {T : Triang 1} {u v a b c : ℕ} (hw : WF T u v)
    (h : (a, b, c) ∈ T.nodes) :
    ∃ T₁ T₂ : Triang 1, WF T₁ a b ∧ WF T₂ b c ∧
      T₁.nodes ⊆ T.nodes ∧ T₂.nodes ⊆ T.nodes := by
  induction T generalizing u v with
  | edge x => simp [nodes_edge] at h
  | node x y z l r ihl ihr =>
    obtain ⟨rfl, rfl, hl, hr⟩ := hw
    rw [nodes_node] at h
    rcases List.mem_cons.mp h with h | h
    · simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2, h3⟩ := h
      subst h1; subst h2; subst h3
      exact ⟨l, r, hl, hr, fun t ht => mem_nodes_left ht, fun t ht => mem_nodes_right ht⟩
    · rcases List.mem_append.mp h with h | h
      · obtain ⟨T₁, T₂, hw1, hw2, hs1, hs2⟩ := ihl hl h
        exact ⟨T₁, T₂, hw1, hw2, fun t ht => mem_nodes_left (hs1 ht),
          fun t ht => mem_nodes_left (hs2 ht)⟩
      · obtain ⟨T₁, T₂, hw1, hw2, hs1, hs2⟩ := ihr hr h
        exact ⟨T₁, T₂, hw1, hw2, fun t ht => mem_nodes_right (hs1 ht),
          fun t ht => mem_nodes_right (hs2 ht)⟩

end Triang

/-- The regular `n`-gon admits a triangulation into isosceles triangles:
there is a triangulation tree on `[0, n-1]` (with unit step and the
wrap-around side `{0, n-1}` implicit at the root) all of whose triangles
are isosceles. -/
def Works (n : ℕ) : Prop := ∃ T : Triang 1, T.WF 0 (n - 1) ∧ T.AllIso n

/-!
## The backward direction: `Works n → n = 2^a (2^b + 1)`
-/

namespace Triang

/-- In a triangulation of the full `(2m+1)`-gon (`m ≥ 2`), some triangle
contains exactly one side of the polygon; it must be a "big" triangle,
which provides an isosceles triangulation of a region of width `m`. -/
theorem odd_regionTree {m : ℕ} (hm : 2 ≤ m) {T : Triang 1}
    (hw : WF T 0 (2 * m)) (hiso : AllIso (2 * m + 1) T) :
    ∃ u : ℕ, ∃ T' : Triang 1, u + m ≤ 2 * m ∧ WF T' u (u + m) ∧
      AllIso (2 * m + 1) T' := by
  obtain ⟨a, b, c, hmem, h1⟩ := exists_sideCnt_one (by omega) ⟨m, rfl⟩ hw
  obtain ⟨ha, hab, hbc, hc⟩ := node_mem_bounds (by omega : (0:ℕ) < 1) hw hmem
  have hiso' := hiso a b c hmem
  have hn : 3 ≤ 2 * m + 1 := by omega
  by_cases h2 : b = a + 1 <;> by_cases h3 : c = b + 1 <;> by_cases h4 : a = 0 ∧ c = 2 * m
  · unfold unitCnt wrapCnt at h1
    dsimp only at h1
    split_ifs at h1 <;> omega
  · unfold unitCnt wrapCnt at h1
    dsimp only at h1
    split_ifs at h1 <;> omega
  · unfold unitCnt wrapCnt at h1
    dsimp only at h1
    split_ifs at h1 <;> omega
  · -- big triangle on the right of side `{a, a+1}`: apex `c = a + m + 1`
    obtain h5 | ⟨-, h6⟩ | ⟨h7, h8⟩ :=
      iso_unit_right hn (by omega : a + 1 < c) (by omega : c < 2 * m + 1) (by subst h2; exact hiso')
    · subst h2; omega
    · subst h2
      obtain ⟨T₁, T₂, hw1, hw2, hs1, hs2⟩ := extract_at_node hw hmem
      have hc' : c = a + 1 + m := by omega
      rw [hc'] at hw2
      exact ⟨a + 1, T₂, by omega, hw2, fun x y z hh => hiso x y z (hs2 hh)⟩
    · subst h2
      exact absurd ⟨h7, by omega⟩ h4
  · unfold unitCnt wrapCnt at h1
    dsimp only at h1
    split_ifs at h1 <;> omega
  · -- big triangle on the left of side `{b, b+1}`: apex `a = b - m`
    obtain h5 | ⟨-, h6⟩ | ⟨h7, h8⟩ :=
      iso_unit_left hn (by omega : a < b) (by omega : b + 1 < 2 * m + 1) (by subst h3; exact hiso')
    · subst h3; omega
    · subst h3
      obtain ⟨T₁, T₂, hw1, hw2, hs1, hs2⟩ := extract_at_node hw hmem
      have hbm : b = a + m := by omega
      rw [hbm] at hw1
      exact ⟨a, T₁, by omega, hw1, fun x y z hh => hiso x y z (hs1 hh)⟩
    · subst h3
      exact absurd ⟨h7, by omega⟩ h4
  · -- big triangle on the wrap-around side: apex `b = m`
    obtain ⟨rfl, rfl⟩ := h4
    obtain hb1 | hb2 | hb3 := iso_wrap hn (by omega : 0 < b) (by omega : b < 2 * m) hiso'
    · omega
    · omega
    · have hbm : b = m := by omega
      obtain ⟨T₁, T₂, hw1, hw2, hs1, hs2⟩ := extract_at_node hw hmem
      rw [hbm] at hw1
      have hw1' : WF T₁ 0 (0 + m) := by
        have e : (0 : ℕ) + m = m := by omega
        rw [e]; exact hw1
      exact ⟨0, T₁, by omega, hw1', fun x y z hh => hiso x y z (hs1 hh)⟩
  · unfold unitCnt wrapCnt at h1
    dsimp only at h1
    split_ifs at h1 <;> omega


/-- If the `2m`-gon works, so does the `m`-gon (`m ≥ 3`). -/
theorem works_even_back {m : ℕ} (hm : 3 ≤ m) (h : Works (2 * m)) : Works m := by
  obtain ⟨T, hw, hiso⟩ := h
  cases T with
  | edge a =>
    obtain ⟨h1, h2⟩ := hw
    omega
  | node a k c l r =>
    obtain ⟨rfl, rfl, hl, hr⟩ := hw
    have hk0 : 0 < k := lt_of_wf (by omega : (0:ℕ) < 1) hl
    have hkc : k < 2 * m - 1 := lt_of_wf (by omega : (0:ℕ) < 1) hr
    have hiso' := hiso 0 k (2 * m - 1) (mem_nodes_root 0 k (2 * m - 1) l r)
    obtain h1 | h2 | h3 := iso_wrap (by omega : 3 ≤ 2 * m) hk0 hkc hiso'
    · -- root is the ear `{0, 1, 2m-1}`; analyze the right child
      have hk1 : k = 1 := h1
      subst hk1
      have hw_r : WF r 1 (1 + (2 * m - 2)) := by
        have e : (1 : ℕ) + (2 * m - 2) = 2 * m - 1 := by omega
        rw [e]; exact hr
      obtain ⟨T', hw', hiso'', -⟩ :=
        regionEven_contract hm (by omega : 1 + (2 * m - 2) ≤ 2 * m - 1) hw_r
          (allIso_right hiso)
      refine ⟨halveTree T', ?_,
        allIso_halve_even hw' (by omega : 1 + (2 * m - 2) ≤ 2 * m) hiso''⟩
      have h1w := wf_halve hw'
      have e1 : (1 : ℕ) / 2 = 0 := by omega
      have e2 : (1 + (2 * m - 2)) / 2 = m - 1 := by omega
      rw [e1, e2] at h1w
      exact h1w
    · -- root is the ear `{0, 2m-2, 2m-1}`; analyze the left child
      have hk2 : k = 2 * m - 2 := by omega
      subst hk2
      have hw_l : WF l 0 (0 + (2 * m - 2)) := by
        have e : (0 : ℕ) + (2 * m - 2) = 2 * m - 2 := by omega
        rw [e]; exact hl
      obtain ⟨T', hw', hiso'', -⟩ :=
        regionEven_contract hm (by omega : 0 + (2 * m - 2) ≤ 2 * m - 1) hw_l
          (allIso_left hiso)
      refine ⟨halveTree T', ?_,
        allIso_halve_even hw' (by omega : 0 + (2 * m - 2) ≤ 2 * m) hiso''⟩
      have h1w := wf_halve hw'
      have e1 : (0 : ℕ) / 2 = 0 := by omega
      have e2 : (0 + (2 * m - 2)) / 2 = m - 1 := by omega
      rw [e1, e2] at h1w
      exact h1w
    · omega

/-- If the `(2m+1)`-gon works (`m ≥ 2`), then `m` is a power of two. -/
theorem works_odd_back {m : ℕ} (hm : 2 ≤ m) (h : Works (2 * m + 1)) :
    ∃ k, m = 2 ^ k := by
  obtain ⟨T, hw, hiso⟩ := h
  have hw' : WF T 0 (2 * m) := by
    have e : 2 * m + 1 - 1 = 2 * m := by omega
    rwa [e] at hw
  have hiso' : AllIso (2 * m + 1) T := hiso
  obtain ⟨u, T₁, hum, hw₁, hiso₁⟩ := Triang.odd_regionTree hm hw' hiso'
  obtain ⟨hm2, T₂, hw₂, hiso₂, hsub⟩ := Triang.regionOdd_contract hm hum hw₁ hiso₁
  obtain ⟨m₂, hm₂⟩ := hm2
  have hiso₂' : AllIso (4 * m₂ + 1) T₂ := by
    have e : 4 * m₂ + 1 = 2 * m + 1 := by omega
    rw [e]; exact hiso₂
  have hmid := Triang.allMid_halve_odd hw₂ (by omega : u + m ≤ u + 2 * m₂) hiso₂'
  obtain ⟨k, hk⟩ := Triang.allMid_pow2 (Triang.wf_halve hw₂) hmid
  have hm3 : (u + m) / 2 - u / 2 = m₂ := by omega
  rw [hm3] at hk
  exact ⟨k + 1, by rw [hm₂, hk, pow_succ]; omega⟩

/-- Backward direction: if the regular `n`-gon admits an isosceles
triangulation, then `n = 2^a * (2^b + 1)` for some `a b`. -/
theorem works_back : ∀ n : ℕ, 3 ≤ n → Works n → ∃ a b : ℕ, n = 2 ^ a * (2 ^ b + 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn h
    rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
    · have hm2m : n = 2 * m := by omega
      by_cases hm2 : m = 2
      · subst hm2; subst hm2m
        exact ⟨1, 0, by norm_num⟩
      · have hm3 : 3 ≤ m := by omega
        have hlt : m < n := by omega
        obtain ⟨a, b, hab⟩ := ih m hlt hm3 (works_even_back hm3 (hm2m ▸ h))
        exact ⟨a + 1, b, by rw [hm2m, hab, pow_succ', mul_assoc]⟩
    · have hmn : n = 2 * m + 1 := by omega
      by_cases hm1 : m = 1
      · subst hm1; subst hmn
        exact ⟨0, 1, by norm_num⟩
      · have hm2 : 2 ≤ m := by omega
        obtain ⟨k, hk⟩ := works_odd_back hm2 (hmn ▸ h)
        exact ⟨0, k + 1, by rw [hmn, hk, pow_succ]; omega⟩

end Triang

/-!
## The forward direction: constructions
-/

namespace Triang

/-- The "linear" triangulation of `[0, 2^k]`: every triangle has the
midpoint property. -/
theorem linTri : ∀ k : ℕ, ∃ T : Triang 1, WF T 0 (2 ^ k) ∧ T.AllMid := by
  intro k
  induction k with
  | zero =>
    refine ⟨Triang.edge 0, ⟨rfl, by omega⟩, ?_⟩
    intro a b c h
    simp [nodes_edge] at h
  | succ k ih =>
    obtain ⟨T, hw, hmid⟩ := ih
    refine ⟨Triang.node 0 (2 ^ k) (2 ^ (k + 1)) T (translateTree (2 ^ k) T),
      ⟨rfl, rfl, hw, ?_⟩, ?_⟩
    · have h1 := wf_translate (2 ^ k) hw
      have e1 : (0 : ℕ) + 2 ^ k = 2 ^ k := by omega
      have e2 : 2 ^ k + 2 ^ k = 2 ^ (k + 1) := by rw [pow_succ]; ring
      rwa [e1, e2] at h1
    · intro a b c hmem
      rw [nodes_node] at hmem
      rcases List.mem_cons.mp hmem with h | hmem
      · simp only [Prod.mk.injEq] at h
        obtain ⟨h1, h2, h3⟩ := h
        subst h1; subst h2; subst h3
        rw [pow_succ]; omega
      · rcases List.mem_append.mp hmem with hmem | hmem
        · exact hmid a b c hmem
        · exact allMid_translate (2 ^ k) hmid a b c hmem

/-- Construction for the odd case: if `m₂ = 2^k`, the region `[0, 2m₂]` of
the `(4m₂+1)`-gon has an isosceles triangulation. -/
theorem regionOdd_forward {m₂ k : ℕ} (hk : m₂ = 2 ^ k) :
    ∃ T : Triang 1, WF T 0 (2 * m₂) ∧ AllIso (2 * (2 * m₂) + 1) T := by
  obtain ⟨T, hw, hmid⟩ := linTri k
  subst hk
  refine ⟨inflate (doubleTree T), wf_inflate (wf_double hw), ?_⟩
  have h1 := allIso_double_odd hw (by omega : 2 ^ k ≤ 2 ^ k) hmid
  have e : 4 * 2 ^ k + 1 = 2 * (2 * 2 ^ k) + 1 := by omega
  rw [e] at h1
  exact allIso_inflate (n := 2 * (2 * 2 ^ k) + 1) (wf_double hw)
    (by omega : 2 * 2 ^ k ≤ 2 * (2 * 2 ^ k) + 1 - 1) (by
      have h2k : 0 < (2:ℕ) ^ k := pow_pos (by omega) k
      omega) h1

/-- The triangle itself works. -/
theorem works3 : Works 3 := by
  refine ⟨Triang.node 0 1 2 (Triang.edge 0) (Triang.edge 1),
    ⟨rfl, rfl, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩, ?_⟩
  intro a b c h
  rw [nodes_node] at h
  rcases List.mem_cons.mp h with h | h
  · simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2, h3⟩ := h
    subst h1; subst h2; subst h3
    left
    rw [cd_one (by omega) (by omega), cd_one (by omega) (by omega)]
  · simp [nodes_edge] at h

/-- The square works (split along a diagonal). -/
theorem works4 : Works 4 := by
  refine ⟨Triang.node 0 2 3 (Triang.node 0 1 2 (Triang.edge 0) (Triang.edge 1))
    (Triang.edge 2), ⟨rfl, rfl, ⟨rfl, rfl, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩, ⟨rfl, rfl⟩⟩, ?_⟩
  intro a b c h
  rw [nodes_node] at h
  rcases List.mem_cons.mp h with h | h
  · simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2, h3⟩ := h
    subst h1; subst h2; subst h3
    right; left
    rw [cd_one (by omega) (by omega), cd_comm 4 3 0]
    have e : cd 4 0 3 = 1 := cd_wrap (by omega)
    rw [e]
  · rcases List.mem_append.mp h with h | h
    · rw [nodes_node] at h
      rcases List.mem_cons.mp h with h | h
      · simp only [Prod.mk.injEq] at h
        obtain ⟨h1, h2, h3⟩ := h
        subst h1; subst h2; subst h3
        left
        rw [cd_one (by omega) (by omega), cd_one (by omega) (by omega)]
      · simp [nodes_edge] at h
    · simp [nodes_edge] at h

/-- Doubling: if the `m`-gon works, so does the `2m`-gon. -/
theorem works_double {m : ℕ} (hm : 3 ≤ m) (h : Works m) : Works (2 * m) := by
  obtain ⟨T, hw, hiso⟩ := h
  refine ⟨Triang.node 0 (2 * m - 2) (2 * m - 1)
    (Triang.inflate (Triang.doubleTree T)) (Triang.edge (2 * m - 2)), ?_, ?_⟩
  · refine ⟨rfl, rfl, ?_, ⟨rfl, by omega⟩⟩
    have h1 := wf_double hw
    have h2 := wf_inflate h1
    have e : 2 * (m - 1) = 2 * m - 2 := by omega
    rwa [e] at h2
  · have h1 := allIso_double (by omega : (0:ℕ) < 1) hw (by omega : m - 1 ≤ m) hiso
    have h2 := allIso_inflate (n := 2 * m) (wf_double hw)
      (by omega : 2 * (m - 1) ≤ 2 * m - 1) (by omega) h1
    intro a b c hmem
    rw [nodes_node] at hmem
    rcases List.mem_cons.mp hmem with hmem | hmem
    · simp only [Prod.mk.injEq] at hmem
      obtain ⟨h1, h2', h3⟩ := hmem
      subst h1; subst h2'; subst h3
      right; left
      have e1 : cd (2 * m) (2 * m - 2) (2 * m - 1) = 1 := by
        rw [cd_of_lt (by omega) (by omega)]
        have g1 : 2 * m - 1 - (2 * m - 2) = 1 := by omega
        rw [g1, min_eq_left (by omega)]
      have e2 : cd (2 * m) (2 * m - 1) 0 = 1 := by
        rw [cd_comm (2 * m) (2 * m - 1) 0]
        exact cd_wrap (by omega)
      rw [e1, e2]
    · rcases List.mem_append.mp hmem with hmem | hmem
      · exact h2 a b c hmem
      · simp [nodes_edge] at hmem

/-- The `(2^b + 1)`-gon works for `b ≥ 2`: the big triangle
`{0, 2^(b-1), 2^b}` plus two copies of the region construction. -/
theorem works_odd_forward {b : ℕ} (hb : 2 ≤ b) : Works (2 ^ b + 1) := by
  obtain ⟨m₂, hm₂⟩ : ∃ m₂, 2 ^ (b - 1) = 2 * m₂ := by
    refine ⟨2 ^ (b - 2), ?_⟩
    have e : b - 1 = b - 2 + 1 := by omega
    rw [e, pow_succ]
    omega
  have hm₂' : m₂ = 2 ^ (b - 2) := by
    have e : 2 ^ (b - 1) = 2 * 2 ^ (b - 2) := by
      have e1 : b - 1 = b - 2 + 1 := by omega
      rw [e1, pow_succ]
      omega
    omega
  obtain ⟨R, hwR, hisoR⟩ := regionOdd_forward (m₂ := m₂) (k := b - 2) hm₂'
  have e2b : 2 ^ b = 2 * (2 * m₂) := by
    have e2 : b = b - 1 + 1 := by omega
    rw [e2, pow_succ', hm₂]
  refine ⟨Triang.node 0 (2 * m₂) (2 * (2 * m₂)) R (translateTree (2 * m₂) R), ?_, ?_⟩
  · have e1 : 2 ^ b + 1 - 1 = 2 * (2 * m₂) := by omega
    rw [e1]
    refine ⟨rfl, rfl, hwR, ?_⟩
    have h1 := wf_translate (2 * m₂) hwR
    have e2 : (0 : ℕ) + 2 * m₂ = 2 * m₂ := by omega
    have e3 : 2 * m₂ + 2 * m₂ = 2 * (2 * m₂) := by omega
    rwa [e2, e3] at h1
  · have e1 : 2 ^ b + 1 = 2 * (2 * m₂) + 1 := by omega
    rw [e1]
    intro a b c hmem
    rw [nodes_node] at hmem
    rcases List.mem_cons.mp hmem with hmem | hmem
    · simp only [Prod.mk.injEq] at hmem
      obtain ⟨h1, h2, h3⟩ := hmem
      subst h1; subst h2; subst h3
      left
      have hm₂pos : 1 ≤ m₂ := by
        rw [hm₂']
        exact Nat.one_le_pow _ 2 (by omega)
      have e2 : cd (2 * (2 * m₂) + 1) 0 (2 * m₂) = 2 * m₂ := by
        rw [cd_of_lt (by omega) (by omega)]
        have g1 : 2 * m₂ - 0 = 2 * m₂ := by omega
        have g2 : 2 * (2 * m₂) + 1 - 2 * m₂ = 2 * m₂ + 1 := by omega
        rw [g1, g2, min_eq_left (by omega)]
      have e3 : cd (2 * (2 * m₂) + 1) (2 * m₂) (2 * (2 * m₂)) = 2 * m₂ := by
        rw [cd_of_lt (by omega) (by omega)]
        have g1 : 2 * (2 * m₂) - 2 * m₂ = 2 * m₂ := by omega
        have g2 : 2 * (2 * m₂) + 1 - 2 * m₂ = 2 * m₂ + 1 := by omega
        rw [g1, g2, min_eq_left (by omega)]
      rw [e2, e3]
    · rcases List.mem_append.mp hmem with hmem | hmem
      · exact hisoR a b c hmem
      · exact allIso_translate (2 * m₂) hisoR a b c hmem

/-- If `m` works, every `2^a * m` works. -/
theorem works_pow_mul {m : ℕ} (h : Works m) (hm : 3 ≤ m) :
    ∀ a : ℕ, Works (2 ^ a * m) := by
  intro a
  induction a with
  | zero =>
    rwa [pow_zero, one_mul]
  | succ a ih =>
    rw [pow_succ, mul_assoc, mul_left_comm]
    exact works_double (by
      have h2a : 0 < 2 ^ a := pow_pos (by omega) a
      have hle : m ≤ 2 ^ a * m := Nat.le_mul_of_pos_left m h2a
      omega) ih

/-- Forward direction: every `n = 2^a * (2^b + 1)` with `n ≥ 3` works. -/
theorem works_forward {n : ℕ} (hn : 3 ≤ n) :
    (∃ a b : ℕ, n = 2 ^ a * (2 ^ b + 1)) → Works n := by
  rintro ⟨a, b, rfl⟩
  by_cases hb0 : b = 0
  · subst hb0
    have ha1 : 1 ≤ a := by
      by_contra hcon
      push Not at hcon
      have hz : a = 0 := by omega
      subst hz
      norm_num at hn
    have e : 2 ^ a * (2 ^ 0 + 1) = 2 ^ (a - 1) * 4 := by
      have e2 : 2 ^ a = 2 * 2 ^ (a - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      rw [e2]
      ring
    rw [e]
    exact works_pow_mul works4 (by omega) (a - 1)
  · have hb1 : 1 ≤ b := by omega
    have hbase : Works (2 ^ b + 1) := by
      by_cases hb1' : b = 1
      · subst hb1'
        exact works3
      · exact works_odd_forward (by omega)
    have hbase3 : 3 ≤ 2 ^ b + 1 := by
      have h2b : 2 ≤ 2 ^ b := by
        have e : b = b - 1 + 1 := by omega
        rw [e, pow_succ']
        have h1 := Nat.one_le_pow (b - 1) 2 (by omega)
        omega
      omega
    exact works_pow_mul hbase hbase3 a

end Triang


snip end

/-- The possible values of `n`: numbers of the form `2^a * (2^b + 1)`. -/
determine answer : Set ℕ := { n | ∃ a b : ℕ, n = 2 ^ a * (2 ^ b + 1) }

problem usa2008_p4 (n : ℕ) (hn : 3 ≤ n) :
    Works n ↔ n ∈ answer := by
  constructor
  · intro h
    obtain ⟨a, b, hab⟩ := Triang.works_back n hn h
    exact ⟨a, b, hab⟩
  · intro h
    exact Triang.works_forward hn h

end Usa2008P4
