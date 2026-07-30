/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Data.List.Triplewise
public import Mathlib.Geometry.Euclidean.Basic
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# USA Mathematical Olympiad 1997, Problem 4

To clip a convex $n$-gon means to choose a pair of consecutive sides $AB$, $BC$
and to replace them by the three segments $AM$, $MN$, and $NC$, where $M$ is the
midpoint of $AB$ and $N$ is the midpoint of $BC$. In other words, one cuts the
triangle $MBN$ off the polygon to obtain a convex $(n+1)$-gon. A regular hexagon
$P_6$ of area $1$ is clipped to obtain a heptagon $P_7$. Then $P_7$ is clipped
(in one of the seven possible ways) to obtain an octagon $P_8$, and so on.
Prove that no matter how the clippings are done, the area of $P_n$ is greater
than $1/3$, for all $n \geq 6$.
-/

namespace Usa1997P4

snip begin

/-! ### Points, cross products and signed area -/

/-- Points in the Euclidean plane. -/
abbrev Pt := EuclideanSpace ℝ (Fin 2)

/-- The 2-dimensional cross product: the signed area of the parallelogram
spanned by two vectors. -/
def cr (a b : Pt) : ℝ := a 0 * b 1 - a 1 * b 0

/-- Twice the signed area of the triangle `a b c`
(positive when `a b c` is oriented counterclockwise). -/
def S (a b c : Pt) : ℝ := cr (b - a) (c - a)

lemma cr_self (a : Pt) : cr a a = 0 := by simp [cr]; ring

lemma cr_add_left (a b c : Pt) : cr (a + b) c = cr a c + cr b c := by
  simp [cr]; ring

lemma cr_add_right (a b c : Pt) : cr a (b + c) = cr a b + cr a c := by
  simp [cr]; ring

lemma cr_smul_left (t : ℝ) (a b : Pt) : cr (t • a) b = t * cr a b := by
  simp [cr]; ring

lemma cr_smul_right (t : ℝ) (a b : Pt) : cr a (t • b) = t * cr a b := by
  simp [cr]; ring

lemma cr_neg_left (a b : Pt) : cr (-a) b = -cr a b := by
  simp [cr]; ring

lemma cr_neg_right (a b : Pt) : cr a (-b) = -cr a b := by
  simp [cr]; ring

lemma cr_sub_left (a b c : Pt) : cr (a - b) c = cr a c - cr b c := by
  simp [cr]; ring

lemma cr_sub_right (a b c : Pt) : cr a (b - c) = cr a b - cr a c := by
  simp [cr]; ring

lemma cr_comm (a b : Pt) : cr a b = -cr b a := by simp [cr]; ring

/-- Expansion of the signed area as a sum of cross products. -/
lemma S_eq_cr_add (a b c : Pt) : S a b c = cr a b + cr b c + cr c a := by
  simp [S, cr]; ring

lemma S_cyclic (a b c : Pt) : S a b c = S b c a := by
  rw [S_eq_cr_add, S_eq_cr_add]; ring

lemma S_self_left (a b : Pt) : S a a b = 0 := by rw [S_eq_cr_add, cr_self, cr_comm]; ring

lemma S_self_right (a b : Pt) : S a b b = 0 := by rw [S_eq_cr_add, cr_self, cr_comm]; ring

lemma S_self_mid (a b : Pt) : S a b a = 0 := by rw [S_cyclic a b a, S_self_right]

lemma S_swap_right (a b c : Pt) : S a c b = -S a b c := by
  rw [S_eq_cr_add, S_eq_cr_add, cr_comm b c, cr_comm c a, cr_comm b a]; ring

/-- `S` is affine in the third argument. -/
lemma S_convexCombo₃ (w : ℝ) (a b c d : Pt) :
    S a b ((1 - w) • c + w • d) = (1 - w) * S a b c + w * S a b d := by
  simp [S, cr]
  ring

/-- `S` is affine in the second argument. -/
lemma S_convexCombo₂ (w : ℝ) (a b c d : Pt) :
    S a ((1 - w) • c + w • d) b = (1 - w) * S a c b + w * S a d b := by
  simp [S, cr]
  ring

/-- `S` is affine in the first argument. -/
lemma S_convexCombo₁ (w : ℝ) (a b c d : Pt) :
    S ((1 - w) • c + w • d) a b = (1 - w) * S c a b + w * S d a b := by
  simp [S, cr]
  ring


/-! ### Shoelace formula -/

/-- Twice the signed area of a polygon given by its vertex list:
the sum of cross products of consecutive (cyclically) adjacent vertices. -/
def shoelace (l : List Pt) : ℝ := (l.zipWith cr (l.rotate 1)).sum

/-- Sum of cross products of consecutive (non-cyclically) adjacent vertices. -/
def consecSum (l : List Pt) : ℝ := (l.zipWith cr l.tail).sum

lemma zipWith_tail_append_singleton (f : Pt → Pt → ℝ) (x : Pt) (l : List Pt) (hl : l ≠ []) :
    l.zipWith f (l.tail ++ [x]) = l.zipWith f l.tail ++ [f (l.getLast hl) x] := by
  induction l with
  | nil => exact absurd rfl hl
  | cons a rest ih =>
    cases rest with
    | nil => simp
    | cons b rest =>
      have ih' := ih (by simp)
      simp only [List.tail_cons] at ih' ⊢
      simp only [List.cons_append, List.zipWith_cons_cons, ih', List.cons_append]
      rw [List.getLast_cons (show b :: rest ≠ [] by simp)]

lemma zipWith_cons_append_singleton (f : Pt → Pt → ℝ) (x : Pt) (l : List Pt) (hl : l ≠ []) :
    (x :: l).zipWith f (l ++ [x]) =
      f x (l.head hl) :: (l.zipWith f l.tail ++ [f (l.getLast hl) x]) := by
  cases l with
  | nil => exact absurd rfl hl
  | cons a rest =>
    have h := zipWith_tail_append_singleton f x (a :: rest) (by simp)
    rw [List.tail_cons] at h
    simp only [List.head_cons, List.cons_append, List.zipWith_cons_cons]
    rw [h]
    simp only [List.tail_cons]

lemma shoelace_cons (x : Pt) (l : List Pt) (hl : l ≠ []) :
    shoelace (x :: l) = cr x (l.head hl) + consecSum l + cr (l.getLast hl) x := by
  rw [shoelace, List.rotate_cons_succ, List.rotate_zero,
    zipWith_cons_append_singleton cr x l hl, List.sum_cons, List.sum_append, consecSum]
  rw [List.sum_singleton]
  ac_rfl

/-- The fan sum: sum of signed triangle areas `S x l[i] l[i+1]` over
consecutive pairs of `l`. -/
def fanSum (x : Pt) (l : List Pt) : ℝ := (l.zipWith (fun a b => S x a b) l.tail).sum

lemma fanSum_cons_cons (x a b : Pt) (rest : List Pt) :
    fanSum x (a :: b :: rest) = S x a b + fanSum x (b :: rest) := by
  simp [fanSum]

lemma fanSum_eq (x : Pt) (l : List Pt) (hl : l ≠ []) :
    fanSum x l = cr x (l.head hl) + consecSum l + cr (l.getLast hl) x := by
  induction l with
  | nil => exact absurd rfl hl
  | cons a rest ih =>
    cases rest with
    | nil =>
      have h1 : fanSum x [a] = 0 := rfl
      have h2 : consecSum [a] = 0 := rfl
      rw [h1, h2, List.getLast_singleton, List.head_cons, cr_comm a x]
      ring
    | cons b rest =>
      have ih' := ih (by simp)
      rw [fanSum_cons_cons, ih']
      have hcs : consecSum (a :: b :: rest) = cr a b + consecSum (b :: rest) := by
        simp [consecSum]
      rw [hcs]
      simp only [List.head_cons]
      rw [List.getLast_cons (show b :: rest ≠ [] by simp), S_eq_cr_add, cr_comm b x]
      ring

/-- The fan identity: the shoelace sum equals the fan sum from the first vertex. -/
lemma shoelace_eq_fanSum (x : Pt) (l : List Pt) (hl : l ≠ []) :
    shoelace (x :: l) = fanSum x l := by
  rw [shoelace_cons x l hl, fanSum_eq x l hl]

lemma shoelace_rotate (l : List Pt) (k : ℕ) : shoelace (l.rotate k) = shoelace l := by
  rw [shoelace, List.rotate_rotate, Nat.add_comm k 1, ← List.rotate_rotate,
    ← List.zipWith_rotate_distrib cr l (l.rotate 1) k (by simp)]
  exact ((List.zipWith cr l (l.rotate 1)).rotate_perm k).sum_eq

/-! ### Convex position -/

/-- A vertex list is in (strict, counterclockwise) convex position if every
increasing triple of vertices makes a left turn. -/
def ConvexPos (l : List Pt) : Prop := l.Triplewise fun a b c => 0 < S a b c

lemma ConvexPos.of_triplewise (l : List Pt) :
    ConvexPos l ↔ ∀ i j k : ℕ, ∀ (hij : i < j) (hjk : j < k) (hk : k < l.length),
      0 < S (l[i]'(by omega)) (l[j]'(by omega)) (l[k]'(hk)) := by
  rw [ConvexPos, List.triplewise_iff_getElem]

/-- Any cyclically ordered triple of a convex-position list has positive area. -/
lemma ConvexPos.cyc {l : List Pt} (h : ConvexPos l) {x y z : ℕ}
    (hx : x < l.length) (hy : y < l.length) (hz : z < l.length)
    (hord : (x < y ∧ y < z) ∨ (y < z ∧ z < x) ∨ (z < x ∧ x < y)) :
    0 < S (l[x]'(hx)) (l[y]'(hy)) (l[z]'(hz)) := by
  rw [ConvexPos.of_triplewise] at h
  rcases hord with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact h x y z h1 h2 hz
  · rw [S_cyclic (l[x]'(hx)) (l[y]'(hy)) (l[z]'(hz))]
    exact h y z x h1 h2 hx
  · rw [S_cyclic (l[x]'(hx)) (l[y]'(hy)) (l[z]'(hz)),
      S_cyclic (l[y]'(hy)) (l[z]'(hz)) (l[x]'(hx))]
    exact h z x y h1 h2 hy

/-- Rotating a convex-position list by at most its length preserves convex position. -/
lemma ConvexPos.rotate_of_le {l : List Pt} (h : ConvexPos l) {k : ℕ} (hk : k ≤ l.length) :
    ConvexPos (l.rotate k) := by
  rw [ConvexPos.of_triplewise]
  intro i j m hij hjm hm
  simp only [List.length_rotate] at hm
  have hn : 0 < l.length := by omega
  have e1 : (l.rotate k)[i]'(by rw [List.length_rotate]; omega) =
      l[(i + k) % l.length]'(Nat.mod_lt _ hn) :=
    List.getElem_rotate l k i (by rw [List.length_rotate]; omega)
  have e2 : (l.rotate k)[j]'(by rw [List.length_rotate]; omega) =
      l[(j + k) % l.length]'(Nat.mod_lt _ hn) :=
    List.getElem_rotate l k j (by rw [List.length_rotate]; omega)
  have e3 : (l.rotate k)[m]'(by rw [List.length_rotate]; omega) =
      l[(m + k) % l.length]'(Nat.mod_lt _ hn) :=
    List.getElem_rotate l k m (by rw [List.length_rotate]; omega)
  rw [e1, e2, e3]
  apply ConvexPos.cyc h (Nat.mod_lt _ hn) (Nat.mod_lt _ hn) (Nat.mod_lt _ hn)
  rcases Nat.lt_or_ge (i + k) l.length with h1 | h1 <;>
    rcases Nat.lt_or_ge (j + k) l.length with h2 | h2 <;>
    rcases Nat.lt_or_ge (m + k) l.length with h3 | h3 <;>
    (try rw [Nat.mod_eq_of_lt h1]) <;> (try rw [Nat.mod_eq_of_lt h2]) <;>
    (try rw [Nat.mod_eq_of_lt h3]) <;>
    (try rw [Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt (show i + k - l.length < l.length by omega)]) <;>
    (try rw [Nat.mod_eq_sub_mod h2, Nat.mod_eq_of_lt (show j + k - l.length < l.length by omega)]) <;>
    (try rw [Nat.mod_eq_sub_mod h3, Nat.mod_eq_of_lt (show m + k - l.length < l.length by omega)]) <;>
    omega

/-- Rotating a convex-position list preserves convex position. -/
lemma ConvexPos.rotate {l : List Pt} (h : ConvexPos l) (k : ℕ) :
    ConvexPos (l.rotate k) := by
  rcases l with - | ⟨hd, tl⟩
  · simp [ConvexPos]
  · rw [← List.rotate_mod]
    exact ConvexPos.rotate_of_le h (Nat.mod_lt _ (by simp)).le


/-! ### The reference regular hexagon -/

/-- The scale factor making the reference hexagon have area 1. -/
noncomputable def scale : ℝ := Real.sqrt (2 / (3 * Real.sqrt 3))

lemma scale_pos : 0 < scale := Real.sqrt_pos.2 (by positivity)
lemma scale_sq : scale ^ 2 = 2 / (3 * Real.sqrt 3) := Real.sq_sqrt (by positivity)
lemma scale_ne_zero : scale ≠ 0 := ne_of_gt scale_pos

lemma cr_smul_smul (t : ℝ) (a b : Pt) : cr (t • a) (t • b) = t ^ 2 * cr a b := by
  rw [cr_smul_left, cr_smul_right]; ring

lemma S_smul (t : ℝ) (a b c : Pt) : S (t • a) (t • b) (t • c) = t ^ 2 * S a b c := by
  simp only [S, ← smul_sub]
  rw [cr_smul_smul]

open scoped EuclideanGeometry Fin

/-- Extensionality for points by coordinates. -/
lemma pt_ext {x y : Pt} (h0 : x 0 = y 0) (h1 : x 1 = y 1) : x = y := by
  rw [WithLp.ext_iff]
  funext i
  fin_cases i
  exacts [h0, h1]

/-- The unit regular hexagon vertices, counterclockwise, with `V 0 = (1, 0)`. -/
noncomputable def hexV : Fin 6 → Pt :=
  ![!₂[1, 0], !₂[1/2, Real.sqrt 3 / 2], !₂[-1/2, Real.sqrt 3 / 2], !₂[-1, 0],
    !₂[-1/2, -(Real.sqrt 3 / 2)], !₂[1/2, -(Real.sqrt 3 / 2)]]

/-- Vertices of the reference regular hexagon of area 1. -/
noncomputable def hexVtx (i : Fin 6) : Pt := scale • hexV i

/-- The inner hexagon: `innerV c` is at one third of the short diagonal
from `hexV c` to `hexV (c+2)`. -/
noncomputable def innerV : Fin 6 → Pt :=
  ![!₂[1/2, Real.sqrt 3 / 6], !₂[0, Real.sqrt 3 / 3], !₂[-1/2, Real.sqrt 3 / 6],
    !₂[-1/2, -(Real.sqrt 3 / 6)], !₂[0, -(Real.sqrt 3 / 3)], !₂[1/2, -(Real.sqrt 3 / 6)]]

/-- Vertices of the inner hexagon (in the same scale). -/
noncomputable def innerVtx (i : Fin 6) : Pt := scale • innerV i

/-- The hexagon as a vertex list. -/
noncomputable def hexagonList : List Pt := List.ofFn hexVtx

/-- The inner hexagon as a vertex list. -/
noncomputable def innerList : List Pt := List.ofFn innerVtx

lemma hexagonList_length : hexagonList.length = 6 := List.length_ofFn

lemma innerList_length : innerList.length = 6 := List.length_ofFn

lemma hexagonList_get (i : ℕ) (hi : i < 6) :
    hexagonList[i]'(by rw [hexagonList_length]; omega) = hexVtx ⟨i, hi⟩ :=
  List.getElem_ofFn _

lemma innerList_get (i : ℕ) (hi : i < 6) :
    innerList[i]'(by rw [innerList_length]; omega) = innerVtx ⟨i, hi⟩ :=
  List.getElem_ofFn _

/-- The inner vertex `I c` is at one third of the diagonal from `V c` to `V (c+2)`. -/
lemma innerVtx_diagonal (i : Fin 6) :
    innerVtx i = hexVtx i + (1/3 : ℝ) • (hexVtx (i + 2) - hexVtx i) := by
  fin_cases i <;> apply pt_ext <;>
    simp [innerVtx, hexVtx, innerV, hexV, smul_sub, smul_eq_mul] <;>
    ring

/-- The inner vertex `I (i+1)` at one third of the diagonal from `V (i+2)`
back to `V i`. -/
lemma innerVtx_succ_diagonal (i : Fin 6) :
    innerVtx (i + 1) = hexVtx (i + 2) + (1/3 : ℝ) • (hexVtx i - hexVtx (i + 2)) := by
  fin_cases i <;> apply pt_ext <;>
    simp [innerVtx, hexVtx, innerV, hexV, smul_sub, smul_eq_mul] <;>
    ring

/-- The inner vertex `I (i+1)` at two thirds of the diagonal from `V i` to `V (i+2)`. -/
lemma innerVtx_succ_diagonal' (i : Fin 6) :
    innerVtx (i + 1) = hexVtx i + (2/3 : ℝ) • (hexVtx (i + 2) - hexVtx i) := by
  fin_cases i <;> apply pt_ext <;>
    simp [innerVtx, hexVtx, innerV, hexV, smul_sub, smul_eq_mul] <;>
    ring

/-- `I i` is on the segment from `V (i-1)` to `V (i+1)`, at two thirds. -/
lemma innerVtx_segment (i : Fin 6) :
    innerVtx i = hexVtx (i - 1) + (2/3 : ℝ) • (hexVtx (i + 1) - hexVtx (i - 1)) := by
  fin_cases i <;> apply pt_ext <;>
    simp [innerVtx, hexVtx, innerV, hexV, smul_sub,
      smul_eq_mul] <;> ring

/-- `I (i-1)` is on the segment from `V (i-1)` to `V (i+1)`, at one third. -/
lemma innerVtx_pred_segment (i : Fin 6) :
    innerVtx (i - 1) = hexVtx (i - 1) + (1/3 : ℝ) • (hexVtx (i + 1) - hexVtx (i - 1)) := by
  fin_cases i <;> apply pt_ext <;>
    simp [innerVtx, hexVtx, innerV, hexV, smul_sub,
      smul_eq_mul] <;> ring

lemma S_hexVtx (a b c : Fin 6) :
    S (hexVtx a) (hexVtx b) (hexVtx c) = scale ^ 2 * S (hexV a) (hexV b) (hexV c) := by
  rw [hexVtx, hexVtx, hexVtx, S_smul]

/-- The unit hexagon is in convex position. -/
lemma S_hexV_pos (i j k : Fin 6) (hij : i < j) (hjk : j < k) :
    0 < S (hexV i) (hexV j) (hexV k) := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp only [Fin.mk_lt_mk] at hij hjk <;>
    first
    | omega
    | (simp [hexV, S, cr]; ring_nf; nlinarith [Real.sqrt_pos.2 (show (0:ℝ) < 3 by norm_num)])

/-- The reference hexagon is in convex position. -/
lemma convexPos_hexagonList : ConvexPos hexagonList := by
  rw [ConvexPos.of_triplewise]
  intro i j k hij hjk hk
  rw [hexagonList_length] at hk
  rw [hexagonList_get i (by omega), hexagonList_get j (by omega),
    hexagonList_get k (by omega), S_hexVtx]
  exact mul_pos (sq_pos_of_ne_zero scale_ne_zero)
    (S_hexV_pos ⟨i, by omega⟩ ⟨j, by omega⟩ ⟨k, by omega⟩ hij hjk)

/-- Twice the signed area of the reference hexagon is `2`, so its area is `1`. -/
lemma shoelace_hexagonList : shoelace hexagonList = 2 := by
  have h : shoelace hexagonList = scale ^ 2 * (3 * Real.sqrt 3) := by
    simp [shoelace, hexagonList, cr, hexVtx, hexV, smul_eq_mul]
    ring_nf
  rw [h, scale_sq]
  field_simp


/-- The midpoint of two points. -/
noncomputable def mid (a b : Pt) : Pt := (1/2 : ℝ) • a + (1/2 : ℝ) • b

lemma mid_combo (a b : Pt) : mid a b = (1 - (1/2 : ℝ)) • a + (1/2 : ℝ) • b := by
  simp only [mid]
  congr 1
  ring

lemma S_mid₁ (u v y z : Pt) : S (mid u v) y z = (S u y z + S v y z) / 2 := by
  rw [mid_combo, S_convexCombo₁]; ring

lemma S_mid₂ (x u v z : Pt) : S x (mid u v) z = (S x u z + S x v z) / 2 := by
  rw [mid_combo, S_convexCombo₂]; ring

lemma S_mid₃ (x y u v : Pt) : S x y (mid u v) = (S x y u + S x y v) / 2 := by
  rw [mid_combo, S_convexCombo₃]; ring

/-- The point at parameter `t` on side `c` of the reference hexagon
(the segment from `V c` to `V (c+1)`). -/
noncomputable def sidePt (c : Fin 6) (t : ℝ) : Pt := hexVtx c + t • (hexVtx (c + 1) - hexVtx c)

/-- `x` lies on the segment from `a` to `b`. -/
def onSeg (x a b : Pt) : Prop := ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ x = a + t • (b - a)

lemma onSeg_sidePt (c : Fin 6) (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    onSeg (sidePt c t) (hexVtx c) (hexVtx (c + 1)) :=
  ⟨t, h0, h1, rfl⟩

/-- The midpoint lies on the segment. -/
lemma onSeg_mid {x y a b : Pt} (hx : onSeg x a b) (hy : onSeg y a b) :
    onSeg (mid x y) a b := by
  obtain ⟨tx, hx0, hx1, rfl⟩ := hx
  obtain ⟨ty, hy0, hy1, rfl⟩ := hy
  refine ⟨(tx + ty) / 2, by linarith, by linarith, ?_⟩
  apply pt_ext <;> simp [mid, smul_add, smul_sub, smul_eq_mul] <;> ring


/-! ### The clipping operation -/

/-- Clip a polygon at vertex `i`: replace it by the midpoints of the two
incident edges. -/
noncomputable def clipAt (l : List Pt) (i : ℕ) (hi : i < l.length) : List Pt :=
  l.take i ++ [mid (l[(i + l.length - 1) % l.length]'(Nat.mod_lt _ (by omega)))
      (l[i]'(hi)),
    mid (l[i]'(hi)) (l[(i + 1) % l.length]'(Nat.mod_lt _ (by omega)))] ++ l.drop (i + 1)

lemma clipAt_length (l : List Pt) (i : ℕ) (hi : i < l.length) :
    (clipAt l i hi).length = l.length + 1 := by
  simp [clipAt, List.length_take]
  omega

lemma getElem_of_getElem? {α : Type*} {l : List α} {i : ℕ} {h : i < l.length} {a : α}
    (he : l[i]? = some a) : l[i]'h = a := by
  have h2 := List.getElem?_eq_getElem h
  rw [he] at h2
  exact Option.some_inj.1 h2.symm

lemma getElem_congr_idx {α : Type*} {l : List α} {i j : ℕ} (hi : i < l.length) (hj : j < l.length)
    (h : i = j) : l[i]'(hi) = l[j]'(hj) := by
  subst h
  rfl

/-- The first midpoint of a clip at index `0`. -/
lemma clipAt_zero_get0 (l : List Pt) (hl : 0 < l.length) :
    (clipAt l 0 (by omega))[0]'(by rw [clipAt_length]; omega) =
      mid (l[(l.length - 1) % l.length]'(Nat.mod_lt _ (by omega))) (l[0]'(by omega)) := by
  apply getElem_of_getElem?
  simp [clipAt]

/-- The second midpoint of a clip at index `0`. -/
lemma clipAt_zero_get1 (l : List Pt) (hl : 0 < l.length) :
    (clipAt l 0 (by omega))[1]'(by rw [clipAt_length]; omega) =
      mid (l[0]'(by omega)) (l[1 % l.length]'(Nat.mod_lt _ (by omega))) := by
  apply getElem_of_getElem?
  simp [clipAt]

/-- Elements past the two midpoints of a clip at index `0`. -/
lemma clipAt_zero_get_ge (l : List Pt) (hl : 0 < l.length) {j : ℕ} (hj : 2 ≤ j)
    (hj2 : j < l.length + 1) :
    (clipAt l 0 (by omega))[j]'(by rw [clipAt_length]; omega) = l[j - 1]'(by omega) := by
  apply getElem_of_getElem?
  have e : clipAt l 0 (by omega) = [mid (l[(l.length - 1) % l.length]'(Nat.mod_lt _ (by omega)))
      (l[0]'(by omega)),
    mid (l[0]'(by omega)) (l[1 % l.length]'(Nat.mod_lt _ (by omega)))] ++ l.drop 1 := by
    simp only [clipAt, List.take_zero, List.nil_append, Nat.zero_add]
  rw [e, List.getElem?_append_right (by simp; omega), List.getElem?_drop]
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd]
  rw [show 1 + (j - 2) = j - 1 from by omega]
  exact List.getElem?_eq_getElem _

/-! ### Computational lemmas: positivity of signed areas between side points -/

/-- Expand a signed area between `sidePt`/`innerVtx` points into a real polynomial
in `scale`, `Real.sqrt 3` and the parameters `t i`, and ring-normalize to close. -/
macro "expandS" : tactic => `(tactic| (
  simp only [S, sidePt, hexVtx, hexV, innerVtx, innerV, cr]
  simp [WithLp.ofLp_smul, WithLp.ofLp_sub, WithLp.ofLp_add, WithLp.ofLp_neg,
    Pi.smul_apply, Pi.sub_apply, Pi.add_apply, Pi.neg_apply, smul_eq_mul, smul_sub, smul_add]
  ring_nf))

lemma S_sidePt_pos_012 {t : Fin 6 → ℝ} (ht : ∀ i : Fin 6, 0 ≤ t i ∧ t i < 1) :
    0 < S (sidePt 0 (t 0)) (sidePt 1 (t 1)) (sidePt 2 (t 2)) := by
  obtain ⟨h00, h01⟩ := ht 0
  obtain ⟨h10, h11⟩ := ht 1
  obtain ⟨h20, h21⟩ := ht 2
  have hEq : S (sidePt 0 (t 0)) (sidePt 1 (t 1)) (sidePt 2 (t 2)) =
      scale ^ 2 * (Real.sqrt 3 / 2) * ((1 - t 0) * (1 - t 1) + t 2 * (t 1 + 1 - t 0)) := by
    expandS
  have hs3 : (0:ℝ) < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have e1 : (0:ℝ) < (1 - t 0) * (1 - t 1) := mul_pos (sub_pos.2 h01) (sub_pos.2 h11)
  have e2 : (0:ℝ) ≤ t 2 * (t 1 + 1 - t 0) := mul_nonneg h20 (by linarith)
  rw [hEq]
  exact mul_pos (mul_pos (pow_pos scale_pos 2) (half_pos hs3)) (by linarith)

lemma S_sidePt_pos_013 {t : Fin 6 → ℝ} (ht : ∀ i : Fin 6, 0 ≤ t i ∧ t i < 1) :
    0 < S (sidePt 0 (t 0)) (sidePt 1 (t 1)) (sidePt 3 (t 3)) := by
  obtain ⟨h00, h01⟩ := ht 0
  obtain ⟨h10, h11⟩ := ht 1
  obtain ⟨h30, h31⟩ := ht 3
  have hEq : S (sidePt 0 (t 0)) (sidePt 1 (t 1)) (sidePt 3 (t 3)) =
      scale ^ 2 * (Real.sqrt 3 / 2) * (2 * (1 - t 0) + t 0 * t 1 + t 1 * t 3) := by
    expandS
  have hs3 : (0:ℝ) < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have e1 : (0:ℝ) < 2 * (1 - t 0) := by linarith
  have e2 : (0:ℝ) ≤ t 0 * t 1 := mul_nonneg h00 h10
  have e3 : (0:ℝ) ≤ t 1 * t 3 := mul_nonneg h10 h30
  rw [hEq]
  exact mul_pos (mul_pos (pow_pos scale_pos 2) (half_pos hs3)) (by linarith)

lemma S_sidePt_pos_014 {t : Fin 6 → ℝ} (ht : ∀ i : Fin 6, 0 ≤ t i ∧ t i < 1) :
    0 < S (sidePt 0 (t 0)) (sidePt 1 (t 1)) (sidePt 4 (t 4)) := by
  obtain ⟨h00, h01⟩ := ht 0
  obtain ⟨h10, h11⟩ := ht 1
  obtain ⟨h40, h41⟩ := ht 4
  have hEq : S (sidePt 0 (t 0)) (sidePt 1 (t 1)) (sidePt 4 (t 4)) =
      scale ^ 2 * (Real.sqrt 3 / 2) * ((1 - t 0) * (1 - t 4) + t 0 * t 1 + (1 - t 0) + t 1) := by
    expandS
  have hs3 : (0:ℝ) < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have e1 : (0:ℝ) < (1 - t 0) * (1 - t 4) := mul_pos (sub_pos.2 h01) (sub_pos.2 h41)
  have e2 : (0:ℝ) ≤ t 0 * t 1 := mul_nonneg h00 h10
  have e3 : (0:ℝ) ≤ 1 - t 0 := sub_nonneg.2 h01.le
  have e4 : (0:ℝ) ≤ t 1 := h10
  rw [hEq]
  exact mul_pos (mul_pos (pow_pos scale_pos 2) (half_pos hs3)) (by linarith)

lemma S_sidePt_pos_015 {t : Fin 6 → ℝ} (ht : ∀ i : Fin 6, 0 ≤ t i ∧ t i < 1) :
    0 < S (sidePt 0 (t 0)) (sidePt 1 (t 1)) (sidePt 5 (t 5)) := by
  obtain ⟨h00, h01⟩ := ht 0
  obtain ⟨h10, h11⟩ := ht 1
  obtain ⟨h50, h51⟩ := ht 5
  have hEq : S (sidePt 0 (t 0)) (sidePt 1 (t 1)) (sidePt 5 (t 5)) =
      scale ^ 2 * (Real.sqrt 3 / 2) * ((1 - t 0) * (1 - t 5) + t 0 * t 1 + t 1 * (1 - t 5)) := by
    expandS
  have hs3 : (0:ℝ) < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have e1 : (0:ℝ) < (1 - t 0) * (1 - t 5) := mul_pos (sub_pos.2 h01) (sub_pos.2 h51)
  have e2 : (0:ℝ) ≤ t 0 * t 1 := mul_nonneg h00 h10
  have e3 : (0:ℝ) ≤ t 1 * (1 - t 5) := mul_nonneg h10 (sub_nonneg.2 h51.le)
  rw [hEq]
  exact mul_pos (mul_pos (pow_pos scale_pos 2) (half_pos hs3)) (by linarith)

lemma S_sidePt_pos_025 {t : Fin 6 → ℝ} (ht : ∀ i : Fin 6, 0 ≤ t i ∧ t i < 1) :
    0 < S (sidePt 0 (t 0)) (sidePt 2 (t 2)) (sidePt 5 (t 5)) := by
  obtain ⟨h00, h01⟩ := ht 0
  obtain ⟨h20, h21⟩ := ht 2
  obtain ⟨h50, h51⟩ := ht 5
  have hEq : S (sidePt 0 (t 0)) (sidePt 2 (t 2)) (sidePt 5 (t 5)) =
      scale ^ 2 * (Real.sqrt 3 / 2) * (2 * (1 - t 5) + t 0 * t 2 + t 0 * t 5) := by
    expandS
  have hs3 : (0:ℝ) < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have e1 : (0:ℝ) < 2 * (1 - t 5) := by linarith
  have e2 : (0:ℝ) ≤ t 0 * t 2 := mul_nonneg h00 h20
  have e3 : (0:ℝ) ≤ t 0 * t 5 := mul_nonneg h00 h50
  rw [hEq]
  exact mul_pos (mul_pos (pow_pos scale_pos 2) (half_pos hs3)) (by linarith)

lemma S_sidePt_pos_034 {t : Fin 6 → ℝ} (ht : ∀ i : Fin 6, 0 ≤ t i ∧ t i < 1) :
    0 < S (sidePt 0 (t 0)) (sidePt 3 (t 3)) (sidePt 4 (t 4)) := by
  obtain ⟨h00, h01⟩ := ht 0
  obtain ⟨h30, h31⟩ := ht 3
  obtain ⟨h40, h41⟩ := ht 4
  have hEq : S (sidePt 0 (t 0)) (sidePt 3 (t 3)) (sidePt 4 (t 4)) =
      scale ^ 2 * (Real.sqrt 3 / 2) * (2 * (1 - t 3) + t 0 * t 4 + t 3 * t 4) := by
    expandS
  have hs3 : (0:ℝ) < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have e1 : (0:ℝ) < 2 * (1 - t 3) := by linarith
  have e2 : (0:ℝ) ≤ t 0 * t 4 := mul_nonneg h00 h40
  have e3 : (0:ℝ) ≤ t 3 * t 4 := mul_nonneg h30 h40
  rw [hEq]
  exact mul_pos (mul_pos (pow_pos scale_pos 2) (half_pos hs3)) (by linarith)

lemma S_sidePt_pos_045 {t : Fin 6 → ℝ} (ht : ∀ i : Fin 6, 0 ≤ t i ∧ t i < 1) :
    0 < S (sidePt 0 (t 0)) (sidePt 4 (t 4)) (sidePt 5 (t 5)) := by
  obtain ⟨h00, h01⟩ := ht 0
  obtain ⟨h40, h41⟩ := ht 4
  obtain ⟨h50, h51⟩ := ht 5
  have hEq : S (sidePt 0 (t 0)) (sidePt 4 (t 4)) (sidePt 5 (t 5)) =
      scale ^ 2 * (Real.sqrt 3 / 2) * ((1 - t 4) * (1 + t 0 - t 5) + t 0 * t 5) := by
    expandS
  have hs3 : (0:ℝ) < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have e1 : (0:ℝ) < (1 - t 4) * (1 + t 0 - t 5) := mul_pos (sub_pos.2 h41) (by linarith)
  have e2 : (0:ℝ) ≤ t 0 * t 5 := mul_nonneg h00 h50
  rw [hEq]
  exact mul_pos (mul_pos (pow_pos scale_pos 2) (half_pos hs3)) (by linarith)

lemma S_sidePt_pos_123 {t : Fin 6 → ℝ} (ht : ∀ i : Fin 6, 0 ≤ t i ∧ t i < 1) :
    0 < S (sidePt 1 (t 1)) (sidePt 2 (t 2)) (sidePt 3 (t 3)) := by
  obtain ⟨h10, h11⟩ := ht 1
  obtain ⟨h20, h21⟩ := ht 2
  obtain ⟨h30, h31⟩ := ht 3
  have hEq : S (sidePt 1 (t 1)) (sidePt 2 (t 2)) (sidePt 3 (t 3)) =
      scale ^ 2 * (Real.sqrt 3 / 2) * ((1 - t 1) * (1 - t 2) + t 3 * (t 2 + 1 - t 1)) := by
    expandS
  have hs3 : (0:ℝ) < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have e1 : (0:ℝ) < (1 - t 1) * (1 - t 2) := mul_pos (sub_pos.2 h11) (sub_pos.2 h21)
  have e2 : (0:ℝ) ≤ t 3 * (t 2 + 1 - t 1) := mul_nonneg h30 (by linarith)
  rw [hEq]
  exact mul_pos (mul_pos (pow_pos scale_pos 2) (half_pos hs3)) (by linarith)

lemma S_sidePt_pos_124 {t : Fin 6 → ℝ} (ht : ∀ i : Fin 6, 0 ≤ t i ∧ t i < 1) :
    0 < S (sidePt 1 (t 1)) (sidePt 2 (t 2)) (sidePt 4 (t 4)) := by
  obtain ⟨h10, h11⟩ := ht 1
  obtain ⟨h20, h21⟩ := ht 2
  obtain ⟨h40, h41⟩ := ht 4
  have hEq : S (sidePt 1 (t 1)) (sidePt 2 (t 2)) (sidePt 4 (t 4)) =
      scale ^ 2 * (Real.sqrt 3 / 2) * (2 * (1 - t 1) + t 1 * t 2 + t 2 * t 4) := by
    expandS
  have hs3 : (0:ℝ) < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have e1 : (0:ℝ) < 2 * (1 - t 1) := by linarith
  have e2 : (0:ℝ) ≤ t 1 * t 2 := mul_nonneg h10 h20
  have e3 : (0:ℝ) ≤ t 2 * t 4 := mul_nonneg h20 h40
  rw [hEq]
  exact mul_pos (mul_pos (pow_pos scale_pos 2) (half_pos hs3)) (by linarith)

lemma S_sidePt_pos_125 {t : Fin 6 → ℝ} (ht : ∀ i : Fin 6, 0 ≤ t i ∧ t i < 1) :
    0 < S (sidePt 1 (t 1)) (sidePt 2 (t 2)) (sidePt 5 (t 5)) := by
  obtain ⟨h10, h11⟩ := ht 1
  obtain ⟨h20, h21⟩ := ht 2
  obtain ⟨h50, h51⟩ := ht 5
  have hEq : S (sidePt 1 (t 1)) (sidePt 2 (t 2)) (sidePt 5 (t 5)) =
      scale ^ 2 * (Real.sqrt 3 / 2) * ((1 - t 1) * (1 - t 5) + t 1 * t 2 + (1 - t 1) + t 2) := by
    expandS
  have hs3 : (0:ℝ) < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have e1 : (0:ℝ) < (1 - t 1) * (1 - t 5) := mul_pos (sub_pos.2 h11) (sub_pos.2 h51)
  have e2 : (0:ℝ) ≤ t 1 * t 2 := mul_nonneg h10 h20
  have e3 : (0:ℝ) ≤ 1 - t 1 := sub_nonneg.2 h11.le
  have e4 : (0:ℝ) ≤ t 2 := h20
  rw [hEq]
  exact mul_pos (mul_pos (pow_pos scale_pos 2) (half_pos hs3)) (by linarith)

lemma S_sidePt_pos_145 {t : Fin 6 → ℝ} (ht : ∀ i : Fin 6, 0 ≤ t i ∧ t i < 1) :
    0 < S (sidePt 1 (t 1)) (sidePt 4 (t 4)) (sidePt 5 (t 5)) := by
  obtain ⟨h10, h11⟩ := ht 1
  obtain ⟨h40, h41⟩ := ht 4
  obtain ⟨h50, h51⟩ := ht 5
  have hEq : S (sidePt 1 (t 1)) (sidePt 4 (t 4)) (sidePt 5 (t 5)) =
      scale ^ 2 * (Real.sqrt 3 / 2) * (2 * (1 - t 4) + t 1 * t 5 + t 4 * t 5) := by
    expandS
  have hs3 : (0:ℝ) < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have e1 : (0:ℝ) < 2 * (1 - t 4) := by linarith
  have e2 : (0:ℝ) ≤ t 1 * t 5 := mul_nonneg h10 h50
  have e3 : (0:ℝ) ≤ t 4 * t 5 := mul_nonneg h40 h50
  rw [hEq]
  exact mul_pos (mul_pos (pow_pos scale_pos 2) (half_pos hs3)) (by linarith)

lemma S_sidePt_pos_234 {t : Fin 6 → ℝ} (ht : ∀ i : Fin 6, 0 ≤ t i ∧ t i < 1) :
    0 < S (sidePt 2 (t 2)) (sidePt 3 (t 3)) (sidePt 4 (t 4)) := by
  obtain ⟨h20, h21⟩ := ht 2
  obtain ⟨h30, h31⟩ := ht 3
  obtain ⟨h40, h41⟩ := ht 4
  have hEq : S (sidePt 2 (t 2)) (sidePt 3 (t 3)) (sidePt 4 (t 4)) =
      scale ^ 2 * (Real.sqrt 3 / 2) * ((1 - t 2) * (1 - t 3) + t 4 * (t 3 + 1 - t 2)) := by
    expandS
  have hs3 : (0:ℝ) < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have e1 : (0:ℝ) < (1 - t 2) * (1 - t 3) := mul_pos (sub_pos.2 h21) (sub_pos.2 h31)
  have e2 : (0:ℝ) ≤ t 4 * (t 3 + 1 - t 2) := mul_nonneg h40 (by linarith)
  rw [hEq]
  exact mul_pos (mul_pos (pow_pos scale_pos 2) (half_pos hs3)) (by linarith)

lemma S_sidePt_pos_235 {t : Fin 6 → ℝ} (ht : ∀ i : Fin 6, 0 ≤ t i ∧ t i < 1) :
    0 < S (sidePt 2 (t 2)) (sidePt 3 (t 3)) (sidePt 5 (t 5)) := by
  obtain ⟨h20, h21⟩ := ht 2
  obtain ⟨h30, h31⟩ := ht 3
  obtain ⟨h50, h51⟩ := ht 5
  have hEq : S (sidePt 2 (t 2)) (sidePt 3 (t 3)) (sidePt 5 (t 5)) =
      scale ^ 2 * (Real.sqrt 3 / 2) * (2 * (1 - t 2) + t 2 * t 3 + t 3 * t 5) := by
    expandS
  have hs3 : (0:ℝ) < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have e1 : (0:ℝ) < 2 * (1 - t 2) := by linarith
  have e2 : (0:ℝ) ≤ t 2 * t 3 := mul_nonneg h20 h30
  have e3 : (0:ℝ) ≤ t 3 * t 5 := mul_nonneg h30 h50
  rw [hEq]
  exact mul_pos (mul_pos (pow_pos scale_pos 2) (half_pos hs3)) (by linarith)

lemma S_sidePt_pos_345 {t : Fin 6 → ℝ} (ht : ∀ i : Fin 6, 0 ≤ t i ∧ t i < 1) :
    0 < S (sidePt 3 (t 3)) (sidePt 4 (t 4)) (sidePt 5 (t 5)) := by
  obtain ⟨h30, h31⟩ := ht 3
  obtain ⟨h40, h41⟩ := ht 4
  obtain ⟨h50, h51⟩ := ht 5
  have hEq : S (sidePt 3 (t 3)) (sidePt 4 (t 4)) (sidePt 5 (t 5)) =
      scale ^ 2 * (Real.sqrt 3 / 2) * ((1 - t 3) * (1 - t 4) + t 5 * (t 4 + 1 - t 3)) := by
    expandS
  have hs3 : (0:ℝ) < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have e1 : (0:ℝ) < (1 - t 3) * (1 - t 4) := mul_pos (sub_pos.2 h31) (sub_pos.2 h41)
  have e2 : (0:ℝ) ≤ t 5 * (t 4 + 1 - t 3) := mul_nonneg h50 (by linarith)
  rw [hEq]
  exact mul_pos (mul_pos (pow_pos scale_pos 2) (half_pos hs3)) (by linarith)

/-! ### Signed areas between a side point and two inner vertices -/

lemma S_sidePt_inner_nonneg_0 {t : Fin 6 → ℝ} (ht : ∀ i : Fin 6, 0 ≤ t i ∧ t i < 1) :
    0 ≤ S (sidePt 0 (t 0)) (innerVtx 1) (innerVtx 0) := by
  obtain ⟨h00, -⟩ := ht 0
  have hEq : S (sidePt 0 (t 0)) (innerVtx 1) (innerVtx 0) =
      scale ^ 2 * (Real.sqrt 3 / 2) * (t 0 / 3) := by
    expandS
  have hs3 : (0:ℝ) < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  rw [hEq]
  exact mul_nonneg (mul_nonneg (pow_pos scale_pos 2).le (half_pos hs3).le) (by linarith)

lemma S_sidePt_inner_nonneg_1 {t : Fin 6 → ℝ} (ht : ∀ i : Fin 6, 0 ≤ t i ∧ t i < 1) :
    0 ≤ S (sidePt 1 (t 1)) (innerVtx 2) (innerVtx 1) := by
  obtain ⟨h10, -⟩ := ht 1
  have hEq : S (sidePt 1 (t 1)) (innerVtx 2) (innerVtx 1) =
      scale ^ 2 * (Real.sqrt 3 / 2) * (t 1 / 3) := by
    expandS
  have hs3 : (0:ℝ) < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  rw [hEq]
  exact mul_nonneg (mul_nonneg (pow_pos scale_pos 2).le (half_pos hs3).le) (by linarith)

lemma S_sidePt_inner_nonneg_2 {t : Fin 6 → ℝ} (ht : ∀ i : Fin 6, 0 ≤ t i ∧ t i < 1) :
    0 ≤ S (sidePt 2 (t 2)) (innerVtx 3) (innerVtx 2) := by
  obtain ⟨h20, -⟩ := ht 2
  have hEq : S (sidePt 2 (t 2)) (innerVtx 3) (innerVtx 2) =
      scale ^ 2 * (Real.sqrt 3 / 2) * (t 2 / 3) := by
    expandS
  have hs3 : (0:ℝ) < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  rw [hEq]
  exact mul_nonneg (mul_nonneg (pow_pos scale_pos 2).le (half_pos hs3).le) (by linarith)

lemma S_sidePt_inner_nonneg_3 {t : Fin 6 → ℝ} (ht : ∀ i : Fin 6, 0 ≤ t i ∧ t i < 1) :
    0 ≤ S (sidePt 3 (t 3)) (innerVtx 4) (innerVtx 3) := by
  obtain ⟨h30, -⟩ := ht 3
  have hEq : S (sidePt 3 (t 3)) (innerVtx 4) (innerVtx 3) =
      scale ^ 2 * (Real.sqrt 3 / 2) * (t 3 / 3) := by
    expandS
  have hs3 : (0:ℝ) < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  rw [hEq]
  exact mul_nonneg (mul_nonneg (pow_pos scale_pos 2).le (half_pos hs3).le) (by linarith)

lemma S_sidePt_inner_nonneg_4 {t : Fin 6 → ℝ} (ht : ∀ i : Fin 6, 0 ≤ t i ∧ t i < 1) :
    0 ≤ S (sidePt 4 (t 4)) (innerVtx 5) (innerVtx 4) := by
  obtain ⟨h40, -⟩ := ht 4
  have hEq : S (sidePt 4 (t 4)) (innerVtx 5) (innerVtx 4) =
      scale ^ 2 * (Real.sqrt 3 / 2) * (t 4 / 3) := by
    expandS
  have hs3 : (0:ℝ) < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  rw [hEq]
  exact mul_nonneg (mul_nonneg (pow_pos scale_pos 2).le (half_pos hs3).le) (by linarith)

lemma S_sidePt_inner_nonneg_5 {t : Fin 6 → ℝ} (ht : ∀ i : Fin 6, 0 ≤ t i ∧ t i < 1) :
    0 ≤ S (sidePt 5 (t 5)) (innerVtx 0) (innerVtx 5) := by
  obtain ⟨h50, -⟩ := ht 5
  have hEq : S (sidePt 5 (t 5)) (innerVtx 0) (innerVtx 5) =
      scale ^ 2 * (Real.sqrt 3 / 2) * (t 5 / 3) := by
    expandS
  have hs3 : (0:ℝ) < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  rw [hEq]
  exact mul_nonneg (mul_nonneg (pow_pos scale_pos 2).le (half_pos hs3).le) (by linarith)

lemma S_sidePt_inner_nonneg (c : Fin 6) {t : Fin 6 → ℝ}
    (ht : ∀ i : Fin 6, 0 ≤ t i ∧ t i < 1) :
    0 ≤ S (sidePt c (t c)) (innerVtx (c + 1)) (innerVtx c) := by
  fin_cases c
  · exact S_sidePt_inner_nonneg_0 ht
  · exact S_sidePt_inner_nonneg_1 ht
  · exact S_sidePt_inner_nonneg_2 ht
  · exact S_sidePt_inner_nonneg_3 ht
  · exact S_sidePt_inner_nonneg_4 ht
  · exact S_sidePt_inner_nonneg_5 ht

lemma S_sidePt_strict_gap {t : Fin 6 → ℝ} (ht : ∀ i : Fin 6, 0 ≤ t i ∧ t i < 1) :
    0 < S (sidePt 0 (t 0)) (innerVtx 0) (innerVtx 5) := by
  obtain ⟨h00, h01⟩ := ht 0
  have hEq : S (sidePt 0 (t 0)) (innerVtx 0) (innerVtx 5) =
      scale ^ 2 * (Real.sqrt 3 / 2) * ((1 - t 0) / 3) := by
    expandS
  have hs3 : (0:ℝ) < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  rw [hEq]
  exact mul_pos (mul_pos (pow_pos scale_pos 2) (half_pos hs3)) (by linarith)


/-- Clipping at index `0` preserves convex position. -/
lemma clipAt_ConvexPos_zero (l : List Pt) (h3 : 3 ≤ l.length) (h : ConvexPos l) :
    ConvexPos (clipAt l 0 (by omega)) := by
  rw [ConvexPos.of_triplewise]
  intro a b c hab hbc hc
  rw [clipAt_length] at hc
  have hn : 0 < l.length := by omega
  have ht := (ConvexPos.of_triplewise l).1 h
  have e1 : l[(l.length - 1) % l.length]'(Nat.mod_lt _ hn) = l[l.length - 1]'(by omega) := by
    apply getElem_of_getElem?
    rw [Nat.mod_eq_of_lt (by omega : l.length - 1 < l.length)]
    exact List.getElem?_eq_getElem _
  have e2 : l[1 % l.length]'(Nat.mod_lt _ hn) = l[1]'(by omega) := by
    apply getElem_of_getElem?
    rw [Nat.mod_eq_of_lt (by omega : 1 < l.length)]
    exact List.getElem?_eq_getElem _
  rcases (by omega : a = 0 ∨ a = 1 ∨ 2 ≤ a) with rfl | rfl | ha
  · -- a = 0
    rw [clipAt_zero_get0 _ hn]
    rcases (by omega : b = 1 ∨ 2 ≤ b) with rfl | hb
    · -- (0, 1, c)
      rw [clipAt_zero_get1 _ hn, clipAt_zero_get_ge _ hn (by omega) (by omega)]
      rw [S_mid₁, S_mid₂, S_mid₂, e1, e2]
      obtain ⟨d, hd⟩ : ∃ d, c = d + 1 := ⟨c - 1, by omega⟩
      subst hd
      simp only [Nat.add_sub_cancel] at *
      have hz : S l[0] l[0] l[d] = 0 := S_self_left _ _
      rcases (by omega : d = 1 ∨ d = l.length - 1 ∨ 1 < d ∧ d < l.length - 1)
        with rfl | rfl | hdd
      · -- c = 2: the first summand is strictly positive
        rw [show S l[l.length - 1] l[1] l[1] = 0 from S_self_right _ _,
          show S l[0] l[1] l[1] = 0 from S_self_right _ _]
        have hs : (0:ℝ) < S l[l.length - 1] l[0] l[1] :=
          ConvexPos.cyc h (x := l.length - 1) (y := 0) (z := 1)
            (by omega) (by omega) (by omega) (by omega)
        linarith
      · -- d = n - 1: the last summand is strictly positive
        rw [show S l[l.length - 1] l[0] l[l.length - 1] = 0 from S_self_mid _ _,
          show S l[l.length - 1] l[1] l[l.length - 1] = 0 from S_self_mid _ _]
        have hs : (0:ℝ) < S l[0] l[1] l[l.length - 1] :=
          ConvexPos.cyc h (x := 0) (y := 1) (z := l.length - 1)
            (by omega) (by omega) (by omega) (by omega)
        linarith
      · -- middle: all summands nonnegative, one strictly positive
        have hs : (0:ℝ) < S l[0] l[1] l[d] :=
          ConvexPos.cyc h (x := 0) (y := 1) (z := d) (by omega) (by omega) (by omega) (by omega)
        have h1' : (0:ℝ) ≤ S l[l.length - 1] l[0] l[d] :=
          (ConvexPos.cyc h (x := l.length - 1) (y := 0) (z := d)
            (by omega) (by omega) (by omega) (by omega)).le
        have h2' : (0:ℝ) ≤ S l[l.length - 1] l[1] l[d] :=
          (ConvexPos.cyc h (x := l.length - 1) (y := 1) (z := d)
            (by omega) (by omega) (by omega) (by omega)).le
        linarith
    · -- (0, b, c) with 2 ≤ b
      rw [clipAt_zero_get_ge _ hn hb (by omega), clipAt_zero_get_ge _ hn (by omega) (by omega)]
      rw [S_mid₁, e1]
      obtain ⟨d, hd⟩ : ∃ d, c = d + 1 := ⟨c - 1, by omega⟩
      obtain ⟨e, he⟩ : ∃ e, b = e + 1 := ⟨b - 1, by omega⟩
      subst hd
      subst he
      simp only [Nat.add_sub_cancel] at *
      have t2 : (0:ℝ) < S l[0] l[e] l[d] :=
        ConvexPos.cyc h (x := 0) (y := e) (z := d) (by omega) (by omega) (by omega) (by omega)
      have t1 : (0:ℝ) ≤ S l[l.length - 1] l[e] l[d] := by
        rcases (by omega : d = l.length - 1 ∨ d < l.length - 1) with hdd | hdd
        · subst hdd
          exact (S_self_mid _ _).ge
        · exact (ConvexPos.cyc h (x := l.length - 1) (y := e) (z := d)
            (by omega) (by omega) (by omega) (by omega)).le
      linarith
  · -- a = 1
    rw [clipAt_zero_get1 _ hn]
    have hb : 2 ≤ b := by omega
    rw [clipAt_zero_get_ge _ hn hb (by omega), clipAt_zero_get_ge _ hn (by omega) (by omega)]
    rw [S_mid₁, e2]
    obtain ⟨d, hd⟩ : ∃ d, c = d + 1 := ⟨c - 1, by omega⟩
    obtain ⟨e, he⟩ : ∃ e, b = e + 1 := ⟨b - 1, by omega⟩
    subst hd
    subst he
    simp only [Nat.add_sub_cancel] at *
    have t1 : (0:ℝ) < S l[0] l[e] l[d] :=
      ConvexPos.cyc h (x := 0) (y := e) (z := d) (by omega) (by omega) (by omega) (by omega)
    have t2 : (0:ℝ) ≤ S l[1] l[e] l[d] := by
      rcases (by omega : e = 1 ∨ 1 < e) with hee | hee
      · subst hee
        exact (S_self_left _ _).ge
      · exact (ConvexPos.cyc h (x := 1) (y := e) (z := d)
          (by omega) (by omega) (by omega) (by omega)).le
    linarith
  · -- 2 ≤ a
    have hb : 2 ≤ b := by omega
    have hc2 : 2 ≤ c := by omega
    rw [clipAt_zero_get_ge _ hn ha (by omega), clipAt_zero_get_ge _ hn hb (by omega),
      clipAt_zero_get_ge _ hn hc2 (by omega)]
    exact ht (a - 1) (b - 1) (c - 1) (by omega) (by omega) (by omega)


/-- Clipping at `i` is, up to rotation, a clip at `0` of the rotated polygon. -/
lemma clipAt_rotate_zero (l : List Pt) (i : ℕ) (hi : i < l.length) (h2 : 2 ≤ l.length) :
    clipAt (l.rotate i) 0 (by simp [List.length_rotate]; omega) = (clipAt l i hi).rotate i := by
  have hn : 0 < l.length := by omega
  have e0 : (l.rotate i)[0]'(by simp [List.length_rotate]; omega) = l[i]'(hi) := by
    apply getElem_of_getElem?
    rw [List.getElem?_rotate (by omega : 0 < l.length), Nat.zero_add, Nat.mod_eq_of_lt hi]
    exact List.getElem?_eq_getElem _
  have e1 : (l.rotate i)[((l.rotate i).length - 1) % (l.rotate i).length]'
      (Nat.mod_lt _ (by simp [List.length_rotate]; omega)) =
      l[(i + l.length - 1) % l.length]'(Nat.mod_lt _ hn) := by
    apply getElem_of_getElem?
    rw [List.length_rotate, Nat.mod_eq_of_lt (by omega : l.length - 1 < l.length),
      List.getElem?_rotate (by omega : l.length - 1 < l.length),
      show (l.length - 1 + i) = i + l.length - 1 from by omega]
    exact List.getElem?_eq_getElem _
  have e2 : (l.rotate i)[1 % (l.rotate i).length]'
      (Nat.mod_lt _ (by simp [List.length_rotate]; omega)) =
      l[(i + 1) % l.length]'(Nat.mod_lt _ hn) := by
    apply getElem_of_getElem?
    rw [List.length_rotate, Nat.mod_eq_of_lt (by omega : 1 < l.length),
      List.getElem?_rotate (by omega : 1 < l.length), Nat.add_comm 1 i]
    exact List.getElem?_eq_getElem _
  have edrop : (l.rotate i).drop 1 = l.drop (i + 1) ++ l.take i := by
    rw [List.rotate_eq_drop_append_take (by omega : i ≤ l.length), List.drop_append,
      List.length_drop, List.drop_drop, show 1 - (l.length - i) = 0 from by omega, List.drop_zero]
  simp only [clipAt, List.take_zero, List.nil_append, Nat.zero_add, e0, e1, e2, edrop]
  conv_rhs => rw [List.append_assoc]
  have hrot := List.rotate_append_length_eq (l.take i)
    ([mid (l[(i + l.length - 1) % l.length]'(Nat.mod_lt _ hn)) (l[i]'(hi)),
      mid (l[i]'(hi)) (l[(i + 1) % l.length]'(Nat.mod_lt _ hn))] ++ l.drop (i + 1))
  rw [List.length_take, Nat.min_eq_left (le_of_lt hi)] at hrot
  rw [hrot, List.append_assoc]

/-- Clipping at any vertex preserves convex position. -/
lemma clipAt_ConvexPos (l : List Pt) (i : ℕ) (hi : i < l.length) (h3 : 3 ≤ l.length)
    (h : ConvexPos l) : ConvexPos (clipAt l i hi) := by
  have hn : 0 < l.length := by omega
  have e : clipAt l i hi = (clipAt (l.rotate i) 0 (by simp [List.length_rotate]; omega)).rotate
      (l.length + 1 - i) := by
    rw [clipAt_rotate_zero l i hi (by omega), List.rotate_rotate,
      show i + (l.length + 1 - i) = (clipAt l i hi).length from by rw [clipAt_length]; omega,
      List.rotate_length]
  rw [e]
  exact (clipAt_ConvexPos_zero (l.rotate i) (by simp [List.length_rotate]; omega)
    (h.rotate i)).rotate _


/-! ### The invariant bundle preserved by clipping -/

/-- The reference hexagon as a set of points. -/
noncomputable def hexSet : Set Pt := convexHull ℝ (Set.range hexVtx)

lemma hexVtx_mem_hexSet (i : Fin 6) : hexVtx i ∈ hexSet := subset_convexHull _ _ ⟨i, rfl⟩

lemma hexSet_convex : Convex ℝ hexSet := convex_convexHull ℝ _

lemma mid_mem_hexSet {x y : Pt} (hx : x ∈ hexSet) (hy : y ∈ hexSet) : mid x y ∈ hexSet := by
  have e : mid x y = x + (1/2 : ℝ) • (y - x) := by
    apply pt_ext <;> simp [mid, smul_sub, smul_eq_mul] <;> ring
  rw [e]
  exact hexSet_convex.add_smul_mem hx (by simpa using hy) ⟨by norm_num, by norm_num⟩

/-- Support invariant: every vertex lies in the hexagon. -/
def SuppInv (l : List Pt) : Prop := ∀ i : ℕ, ∀ hi : i < l.length, l[i]'(hi) ∈ hexSet

lemma SuppInv_rotate {l : List Pt} (k : ℕ) : SuppInv (l.rotate k) ↔ SuppInv l := by
  constructor
  · intro h i hi
    have h2 := h ((i + (l.length - k % l.length)) % l.length)
      (by rw [List.length_rotate]; exact Nat.mod_lt _ (by omega))
    rw [List.getElem_rotate l k _ (by rw [List.length_rotate]; exact Nat.mod_lt _ (by omega))] at h2
    have key : ((i + (l.length - k % l.length)) % l.length + k) % l.length = i := by
      rw [Nat.mod_add_mod,
        show i + (l.length - k % l.length) + k = i + (k - k % l.length) + l.length from by
          have h1 := Nat.mod_lt k (by omega : 0 < l.length)
          have h2 := Nat.mod_le k l.length
          omega, Nat.add_mod_right,
        show k - k % l.length = l.length * (k / l.length) from by
          have := Nat.mod_add_div k l.length
          omega, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi]
    rw [getElem_congr_idx _ _ key] at h2
    exact h2
  · intro h i hi
    rw [List.getElem_rotate l k i (by simpa using hi)]
    exact h _ _

lemma SuppInv_base : SuppInv hexagonList := by
  intro i hi
  rw [hexagonList_length] at hi
  rw [hexagonList_get i hi]
  exact hexVtx_mem_hexSet _

lemma SuppInv_clip_zero {l : List Pt} (h : SuppInv l) (hn : 0 < l.length) :
    SuppInv (clipAt l 0 (by omega)) := by
  intro j hj
  rw [clipAt_length] at hj
  rcases (by omega : j = 0 ∨ j = 1 ∨ 2 ≤ j) with rfl | rfl | hj2
  · rw [clipAt_zero_get0 _ hn]
    exact mid_mem_hexSet (h _ (Nat.mod_lt _ hn)) (h _ hn)
  · rw [clipAt_zero_get1 _ hn]
    exact mid_mem_hexSet (h _ hn) (h _ (Nat.mod_lt _ hn))
  · rw [clipAt_zero_get_ge _ hn hj2 hj]
    exact h _ (by omega)

lemma SuppInv_clip {l : List Pt} (h : SuppInv l) (i : ℕ) (hi : i < l.length)
    (h2 : 2 ≤ l.length) : SuppInv (clipAt l i hi) := by
  have hn : 0 < l.length := by omega
  have e : clipAt l i hi = (clipAt (l.rotate i) 0 (by simp [List.length_rotate]; omega)).rotate
      (l.length + 1 - i) := by
    rw [clipAt_rotate_zero l i hi (by omega), List.rotate_rotate,
      show i + (l.length + 1 - i) = (clipAt l i hi).length from by rw [clipAt_length]; omega,
      List.rotate_length]
  rw [e, SuppInv_rotate]
  exact SuppInv_clip_zero ((SuppInv_rotate i).2 h) (by simp [List.length_rotate]; omega)

/-- Side-pair invariant: side `c` contains two cyclically adjacent vertices. -/
def SidePair (l : List Pt) (c : Fin 6) : Prop :=
  ∃ j : ℕ, ∃ hj : j < l.length,
    onSeg (l[j]'(hj)) (hexVtx c) (hexVtx (c + 1)) ∧
    onSeg (l[(j + 1) % l.length]'(Nat.mod_lt _ (by omega))) (hexVtx c) (hexVtx (c + 1))

lemma SidePair_base (c : Fin 6) : SidePair hexagonList c := by
  refine ⟨c.val, by rw [hexagonList_length]; exact c.isLt, ?_, ?_⟩
  · rw [hexagonList_get c.val c.isLt]
    exact ⟨0, le_refl 0, by norm_num, by simp⟩
  · have key : (c.val + 1) % hexagonList.length = (c + 1).val := by
      rw [hexagonList_length, Fin.val_add, show ((1 : Fin 6).val = 1) from rfl]
    have hj : (c + 1).val < hexagonList.length := by
      rw [hexagonList_length]; exact (c + 1).isLt
    rw [getElem_congr_idx _ hj key, hexagonList_get (c + 1).val (c + 1).isLt, Fin.eta]
    exact ⟨1, by norm_num, le_refl 1, by simp⟩

lemma SidePair_rotate {l : List Pt} {c : Fin 6} (k : ℕ) (hn : 0 < l.length) :
    SidePair (l.rotate k) c ↔ SidePair l c := by
  constructor
  · rintro ⟨j, hj, h1, h2⟩
    simp only [List.length_rotate] at hj h1 h2
    rw [List.getElem_rotate l k j (by simpa using hj)] at h1
    rw [List.getElem_rotate l k ((j + 1) % l.length) (by simpa using Nat.mod_lt _ hn)] at h2
    have key : ((j + k) % l.length + 1) % l.length = ((j + 1) % l.length + k) % l.length := by
      have e1 : ((j + k) % l.length + 1) % l.length = (j + k + 1) % l.length :=
        Nat.mod_add_mod _ _ _
      have e2 : ((j + 1) % l.length + k) % l.length = (j + 1 + k) % l.length :=
        Nat.mod_add_mod _ _ _
      rw [e1, e2, show j + k + 1 = j + 1 + k from by omega]
    exact ⟨(j + k) % l.length, Nat.mod_lt _ hn, h1, by
      rw [getElem_congr_idx _ (Nat.mod_lt _ hn) key]
      exact h2⟩
  · rintro ⟨j, hj, h1, h2⟩
    have key : ((j + (l.length - k % l.length)) % l.length + k) % l.length = j := by
      rw [Nat.mod_add_mod,
        show j + (l.length - k % l.length) + k = j + (k - k % l.length) + l.length from by
          have hh1 := Nat.mod_lt k hn
          have hh2 := Nat.mod_le k l.length
          omega, Nat.add_mod_right,
        show k - k % l.length = l.length * (k / l.length) from by
          have := Nat.mod_add_div k l.length
          omega, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
    have key2 : (((j + (l.length - k % l.length)) % l.length + 1) % l.length + k) % l.length =
        (j + 1) % l.length := by
      have step1 : ((j + (l.length - k % l.length)) % l.length + 1) % l.length =
          (j + (l.length - k % l.length) + 1) % l.length := Nat.mod_add_mod _ _ _
      rw [step1, Nat.mod_add_mod,
        show j + (l.length - k % l.length) + 1 + k = j + 1 + (k - k % l.length) + l.length from by
          have hh1 := Nat.mod_lt k hn
          have hh2 := Nat.mod_le k l.length
          omega, Nat.add_mod_right,
        show k - k % l.length = l.length * (k / l.length) from by
          have := Nat.mod_add_div k l.length
          omega, Nat.add_mul_mod_self_left]
    refine ⟨(j + (l.length - k % l.length)) % l.length,
      by rw [List.length_rotate]; exact Nat.mod_lt _ hn, ?_, ?_⟩
    · rw [List.getElem_rotate l k _ (by rw [List.length_rotate]; exact Nat.mod_lt _ hn),
        getElem_congr_idx _ hj key]
      exact h1
    · rw [getElem_congr_idx _ (by rw [List.length_rotate]; exact Nat.mod_lt _ hn)
        (show ((j + (l.length - k % l.length)) % l.length + 1) % (l.rotate k).length =
          ((j + (l.length - k % l.length)) % l.length + 1) % l.length from by
          rw [List.length_rotate]),
        List.getElem_rotate l k _ (by rw [List.length_rotate]; exact Nat.mod_lt _ hn),
        getElem_congr_idx _ (Nat.mod_lt _ hn) key2]
      exact h2


lemma SidePair_clip_zero {l : List Pt} (c : Fin 6) (h : SidePair l c) (h2 : 2 ≤ l.length) :
    SidePair (clipAt l 0 (by omega)) c := by
  have hn : 0 < l.length := by omega
  obtain ⟨j, hj, h1, h2'⟩ := h
  rcases (by omega : j = 0 ∨ j = l.length - 1 ∨ 0 < j ∧ j < l.length - 1) with rfl | rfl | hj'
  · -- the pair is (l[0], l[1 % n]): becomes (m₂, l[1]) at positions (1, 2)
    rw [getElem_congr_idx _ (Nat.mod_lt _ hn) (show (0 + 1) % l.length = 1 % l.length from by
      rw [Nat.zero_add])] at h2'
    refine ⟨1, by rw [clipAt_length]; omega, ?_, ?_⟩
    · rw [clipAt_zero_get1 _ hn]
      exact onSeg_mid h1 h2'
    · rw [getElem_congr_idx _ (by omega) (Nat.mod_eq_of_lt (by omega : 1 < l.length))] at h2'
      have e : (1 + 1) % (clipAt l 0 (by omega)).length = 2 :=
        Nat.mod_eq_of_lt (by rw [clipAt_length]; omega)
      rw [getElem_congr_idx _ (by rw [clipAt_length]; omega) e,
        clipAt_zero_get_ge _ hn (by omega) (by omega),
        getElem_congr_idx _ (by omega) (by omega : 2 - 1 = 1)]
      exact h2'
  · -- the pair is (l[n-1], l[0]): becomes (l[n-1], m₁) at positions (n, 0)
    rw [getElem_congr_idx _ hn (show (l.length - 1 + 1) % l.length = 0 from by
      rw [Nat.sub_add_cancel (by omega), Nat.mod_self])] at h2'
    refine ⟨l.length, by rw [clipAt_length]; omega, ?_, ?_⟩
    · rw [clipAt_zero_get_ge _ hn (by omega) (by omega),
        getElem_congr_idx _ (by omega) (by omega : l.length - 1 = l.length - 1)]
      exact h1
    · have e : (l.length + 1) % (clipAt l 0 (by omega)).length = 0 := by
        rw [clipAt_length, Nat.mod_self]
      rw [getElem_congr_idx _ (by rw [clipAt_length]; omega) e, clipAt_zero_get0 _ hn]
      rw [← getElem_congr_idx (Nat.mod_lt _ hn) (by omega)
        (Nat.mod_eq_of_lt (by omega : l.length - 1 < l.length))] at h1
      exact onSeg_mid h1 h2'
  · -- the pair is (l[j], l[j+1]) with 0 < j < n-1: becomes the same at positions (j+1, j+2)
    rw [getElem_congr_idx _ (by omega) (Nat.mod_eq_of_lt (by omega : j + 1 < l.length))] at h2'
    refine ⟨j + 1, by rw [clipAt_length]; omega, ?_, ?_⟩
    · rw [clipAt_zero_get_ge _ hn (by omega) (by omega),
        getElem_congr_idx _ (by omega) (by omega : j + 1 - 1 = j)]
      exact h1
    · have e : (j + 1 + 1) % (clipAt l 0 (by omega)).length = j + 2 := by
        rw [clipAt_length, Nat.mod_eq_of_lt (by omega)]
      rw [getElem_congr_idx _ (by rw [clipAt_length]; omega) e,
        clipAt_zero_get_ge _ hn (by omega) (by omega),
        getElem_congr_idx _ (by omega) (by omega : j + 2 - 1 = j + 1)]
      exact h2'

lemma SidePair_clip {l : List Pt} (c : Fin 6) (h : SidePair l c) (i : ℕ) (hi : i < l.length)
    (h2 : 2 ≤ l.length) : SidePair (clipAt l i hi) c := by
  have hn : 0 < l.length := by omega
  have e : clipAt l i hi = (clipAt (l.rotate i) 0 (by simp [List.length_rotate]; omega)).rotate
      (l.length + 1 - i) := by
    rw [clipAt_rotate_zero l i hi (by omega), List.rotate_rotate,
      show i + (l.length + 1 - i) = (clipAt l i hi).length from by rw [clipAt_length]; omega,
      List.rotate_length]
  rw [e]
  have hn' : 0 < (clipAt (l.rotate i) 0 (by simp [List.length_rotate]; omega)).length := by
    rw [clipAt_length, List.length_rotate]; omega
  exact (SidePair_rotate (l.length + 1 - i) hn').2 (SidePair_clip_zero c
    ((SidePair_rotate i hn).2 h) (by simp [List.length_rotate]; omega))

/-! ### Reachability and the main invariant -/

/-- The polygons obtainable from the reference hexagon by repeated clipping. -/
inductive Reachable : List Pt → Prop
  | base : Reachable hexagonList
  | clip {l : List Pt} (i : ℕ) (hi : i < l.length) : Reachable l → Reachable (clipAt l i hi)

/-- The invariant bundle: at least 6 vertices, strict convex position,
all vertices in the hexagon, and an adjacent pair of vertices on each side. -/
def Bundle (l : List Pt) : Prop :=
  6 ≤ l.length ∧ ConvexPos l ∧ SuppInv l ∧ ∀ c : Fin 6, SidePair l c

lemma bundle_base : Bundle hexagonList :=
  ⟨le_refl 6, convexPos_hexagonList, SuppInv_base, SidePair_base⟩

lemma bundle_clip {l : List Pt} (i : ℕ) (hi : i < l.length) (h : Bundle l) :
    Bundle (clipAt l i hi) := by
  obtain ⟨h6, hcp, hsupp, hside⟩ := h
  exact ⟨by rw [clipAt_length]; omega, clipAt_ConvexPos l i hi (by omega) hcp,
    SuppInv_clip hsupp i hi (by omega),
    fun c => SidePair_clip c (hside c) i hi (by omega)⟩

lemma bundle_of_reachable {l : List Pt} (h : Reachable l) : Bundle l := by
  induction h with
  | base => exact bundle_base
  | clip i hi _ ih => exact bundle_clip i hi ih


/-! ### The crossing lemma -/

/-- If `p` is on segment `OP` and `q` on segment `OQ`, with `p`, `q` on opposite
sides of the ray `OX` (where `X` is on segment `PQ`), then segment `pq` meets
segment `OX`. -/
lemma crossing (O P Q X p q : Pt) (u s t : ℝ)
    (_hu0 : 0 ≤ u) (_hu1 : u ≤ 1)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hX : X = P + u • (Q - P))
    (hp : p = O + s • (P - O))
    (hq : q = O + t • (Q - O))
    (hdeg : cr (P - O) (Q - O) ≠ 0)
    (hsp : cr (p - O) (X - O) ≤ 0)
    (hsq : 0 ≤ cr (q - O) (X - O)) :
    ∃ z : Pt, ∃ lam r : ℝ, 0 ≤ lam ∧ lam ≤ 1 ∧ 0 ≤ r ∧ r ≤ 1 ∧
      z = p + lam • (q - p) ∧ z = O + r • (X - O) := by
  have hXO : X - O = (1 - u) • (P - O) + u • (Q - O) := by
    rw [hX]
    module
  have hpO : p - O = s • (P - O) := by rw [hp, add_sub_cancel_left]
  have hqO : q - O = t • (Q - O) := by rw [hq, add_sub_cancel_left]
  have hφp : cr (p - O) (X - O) = s * u * cr (P - O) (Q - O) := by
    rw [hpO, hXO, cr_smul_left, cr_add_right, cr_smul_right, cr_smul_right, cr_self]
    ring
  have hφq : cr (q - O) (X - O) = -(t * (1 - u) * cr (P - O) (Q - O)) := by
    rw [hqO, hXO, cr_smul_left, cr_add_right, cr_smul_right, cr_smul_right, cr_self,
      cr_comm]
    ring
  set D := cr (P - O) (Q - O) with hD
  by_cases hz : cr (p - O) (X - O) = 0 ∧ cr (q - O) (X - O) = 0
  · -- degenerate case: both points lie on the ray
    have hsu : s * u = 0 := by
      have h1 := hz.1
      rw [hφp] at h1
      exact (mul_eq_zero.1 h1).resolve_right hdeg
    have ht1' : t * (1 - u) = 0 := by
      have h2 := hz.2
      rw [hφq] at h2
      have h3 : t * (1 - u) * D = 0 := by linarith
      exact (mul_eq_zero.1 h3).resolve_right hdeg
    rcases mul_eq_zero.1 hsu with hs0' | hu0'
    · -- s = 0: p = O
      refine ⟨p, 0, 0, by norm_num, by norm_num, by norm_num, by norm_num, by simp, ?_⟩
      have hp2 : p = O := by rw [hp, hs0', zero_smul, add_zero]
      rw [hp2]
      simp
    · -- u = 0: then t = 0, q = O
      have ht0' : t = 0 := by rw [hu0', sub_zero, mul_one] at ht1'; exact ht1'
      refine ⟨q, 1, 0, by norm_num, by norm_num, by norm_num, by norm_num, by simp, ?_⟩
      have hq2 : q = O := by rw [hq, ht0', zero_smul, add_zero]
      rw [hq2]
      simp
  · -- generic case
    have hsum : s * u * D + t * (1 - u) * D ≠ 0 := by
      intro hzero
      have h1 : s * u * D ≤ 0 := by linarith
      have h2 : t * (1 - u) * D ≤ 0 := by linarith
      have h3 : s * u * D = 0 := by linarith
      have h4 : t * (1 - u) * D = 0 := by linarith
      exact hz ⟨by rw [hφp]; linarith, by rw [hφq]; linarith⟩
    have hneg : s * u * D + t * (1 - u) * D < 0 :=
      (add_nonpos (by linarith) (by linarith)).lt_of_ne hsum
    set lam := (s * u * D) / (s * u * D + t * (1 - u) * D) with hlam
    have hlam0 : 0 ≤ lam := by
      rw [hlam, ← neg_div_neg_eq]
      exact div_nonneg (by linarith) (by linarith)
    have hlam1 : lam ≤ 1 := by
      rw [hlam, div_le_one_of_neg hneg]
      linarith
    have hlam_eq : lam * (s * u * D + t * (1 - u) * D) = s * u * D := by
      rw [hlam, div_mul_cancel₀ _ hsum]
    have hab : s * (1 - lam) * u = t * lam * (1 - u) := by
      have h4 := hlam_eq
      rw [← add_mul, ← mul_assoc] at h4
      have h5 : lam * (s * u + t * (1 - u)) = s * u :=
        (mul_eq_mul_right_iff.1 h4).resolve_right hdeg
      linarith
    set r := s * (1 - lam) + t * lam with hr
    have hr0 : 0 ≤ r := by
      rw [hr]
      have h1 : 0 ≤ s * (1 - lam) := mul_nonneg hs0 (by linarith)
      have h2 : 0 ≤ t * lam := mul_nonneg ht0 hlam0
      linarith
    have hr1 : r ≤ 1 := by
      rw [hr]
      have h1 : s * (1 - lam) ≤ 1 - lam := by
        have := mul_le_mul_of_nonneg_right hs1 (by linarith : (0:ℝ) ≤ 1 - lam)
        rwa [one_mul] at this
      have h2 : t * lam ≤ lam := by
        have := mul_le_mul_of_nonneg_right ht1 hlam0
        rwa [one_mul] at this
      linarith
    set z := p + lam • (q - p) with hzdef
    have hz2 : z - O = (p - O) + lam • ((q - O) - (p - O)) := by
      rw [hzdef]
      module
    have hzO : z - O = (s * (1 - lam)) • (P - O) + (t * lam) • (Q - O) := by
      rw [hz2, hpO, hqO]
      module
    have hrX : z = O + r • (X - O) := by
      have hkey : r • (X - O) = (s * (1 - lam)) • (P - O) + (t * lam) • (Q - O) := by
        rw [hXO, smul_add, ← mul_smul, ← mul_smul,
          show r * (1 - u) = s * (1 - lam) from by
            rw [hr]
            linear_combination -hab,
          show r * u = t * lam from by
            rw [hr]
            linear_combination hab]
      rw [hkey, ← hzO]
      module
    have hφz : cr (z - O) (X - O) = 0 := by
      have hqp : cr (Q - O) (P - O) = -D := by rw [hD, cr_comm]
      rw [hzO, hXO]
      simp only [cr_add_left, cr_smul_left, cr_add_right, cr_smul_right, cr_self, hqp]
      rw [← hD]
      linear_combination D * hab
    exact ⟨z, lam, r, hlam0, hlam1, hr0, hr1, hzdef, hrX⟩


lemma S_swap_left (a b c : Pt) : S b a c = -S a b c := by simp only [S, cr]; simp; ring

lemma S_neg_swap12 (a b c : Pt) : S a b c = -S b a c := by simp only [S, cr]; simp; ring

/-- The hexagon vertices have positive signed area for any cyclically ordered
triple (in the cyclic order of `Fin 6`). -/
lemma convexPos_hexagonList_cyc {a b c : Fin 6}
    (hord : (a.val < b.val ∧ b.val < c.val) ∨ (b.val < c.val ∧ c.val < a.val) ∨
      (c.val < a.val ∧ a.val < b.val)) :
    0 < S (hexVtx a) (hexVtx b) (hexVtx c) := by
  have h := convexPos_hexagonList.cyc a.isLt b.isLt c.isLt hord
  simp only [hexagonList, List.getElem_ofFn, Fin.eta] at h
  exact h

/-- `I (i-1)` is also at one third of the diagonal from `V i` to `V (i-2)`. -/
lemma innerVtx_pred_diagonal2 (i : Fin 6) :
    innerVtx (i - 1) = hexVtx i + (1/3 : ℝ) • (hexVtx (i - 2) - hexVtx i) := by
  fin_cases i <;> apply pt_ext <;>
    simp [innerVtx, hexVtx, innerV, hexV, smul_sub,
      smul_eq_mul] <;> ring

/-- The crossing lemma specialized to a corner of the hexagon, with `p` on the
left adjacent side and `q` on the right adjacent side. -/
lemma corner_crossing (i : Fin 6) (X : Pt) (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hX : X = hexVtx (i - 1) + u • (hexVtx (i + 1) - hexVtx (i - 1)))
    {t : Fin 6 → ℝ} (ht : ∀ j : Fin 6, 0 ≤ t j ∧ t j < 1)
    (hsp : cr (sidePt (i - 1) (t (i - 1)) - hexVtx i) (X - hexVtx i) ≤ 0)
    (hsq : 0 ≤ cr (sidePt i (t i) - hexVtx i) (X - hexVtx i)) :
    ∃ z : Pt, ∃ lam r : ℝ, 0 ≤ lam ∧ lam ≤ 1 ∧ 0 ≤ r ∧ r ≤ 1 ∧
      z = sidePt (i - 1) (t (i - 1)) + lam • (sidePt i (t i) - sidePt (i - 1) (t (i - 1))) ∧
      z = hexVtx i + r • (X - hexVtx i) := by
  have h1 : (i - 1 + 1 : Fin 6) = i := by fin_cases i <;> rfl
  have hp : sidePt (i - 1) (t (i - 1)) =
      hexVtx i + (1 - t (i - 1)) • (hexVtx (i - 1) - hexVtx i) := by
    rw [sidePt, h1]
    module
  have hpos : 0 < S (hexVtx (i - 1)) (hexVtx i) (hexVtx (i + 1)) :=
    convexPos_hexagonList_cyc (by fin_cases i <;> simp only [Fin.val_add, Fin.val_sub] <;> omega)
  have hdeg : cr (hexVtx (i - 1) - hexVtx i) (hexVtx (i + 1) - hexVtx i) ≠ 0 := by
    have h2 : cr (hexVtx (i - 1) - hexVtx i) (hexVtx (i + 1) - hexVtx i) =
        S (hexVtx i) (hexVtx (i - 1)) (hexVtx (i + 1)) := rfl
    rw [h2, S_neg_swap12]
    linarith
  exact crossing (hexVtx i) (hexVtx (i - 1)) (hexVtx (i + 1)) X
    (sidePt (i - 1) (t (i - 1))) (sidePt i (t i)) u (1 - t (i - 1)) (t i)
    hu0 hu1 (by linarith [(ht (i - 1)).2]) (by linarith [(ht (i - 1)).1])
    (ht i).1 (le_of_lt (ht i).2) hX hp rfl hdeg hsp hsq

/-- Crossing over the chord between the two sides adjacent to corner `i`,
with `X = I i`. -/
lemma corner_crossing_A (i : Fin 6) {t : Fin 6 → ℝ} (ht : ∀ j : Fin 6, 0 ≤ t j ∧ t j < 1) :
    ∃ z : Pt, ∃ lam r : ℝ, 0 ≤ lam ∧ lam ≤ 1 ∧ 0 ≤ r ∧ r ≤ 1 ∧
      z = sidePt (i - 1) (t (i - 1)) + lam • (sidePt i (t i) - sidePt (i - 1) (t (i - 1))) ∧
      z = hexVtx i + r • (innerVtx i - hexVtx i) := by
  have h1 : (i - 1 + 1 : Fin 6) = i := by fin_cases i <;> rfl
  have hsub1 : sidePt (i - 1) (t (i - 1)) - hexVtx i = (1 - t (i - 1)) • (hexVtx (i - 1) - hexVtx i) := by
    rw [sidePt, h1]
    module
  have hsub2 : sidePt i (t i) - hexVtx i = t i • (hexVtx (i + 1) - hexVtx i) := by
    rw [sidePt]
    module
  have hXsub : innerVtx i - hexVtx i = (1/3 : ℝ) • (hexVtx (i + 2) - hexVtx i) := by
    rw [innerVtx_diagonal i]
    module
  have hsp : cr (sidePt (i - 1) (t (i - 1)) - hexVtx i) (innerVtx i - hexVtx i) ≤ 0 := by
    rw [hsub1, hXsub, cr_smul_left, cr_smul_right]
    have hpos : 0 < S (hexVtx (i - 1)) (hexVtx i) (hexVtx (i + 2)) :=
      convexPos_hexagonList_cyc (by fin_cases i <;> simp only [Fin.val_add, Fin.val_sub] <;> omega)
    have hsign : cr (hexVtx (i - 1) - hexVtx i) (hexVtx (i + 2) - hexVtx i) < 0 := by
      have h2 : cr (hexVtx (i - 1) - hexVtx i) (hexVtx (i + 2) - hexVtx i) =
          S (hexVtx i) (hexVtx (i - 1)) (hexVtx (i + 2)) := rfl
      rw [h2, S_neg_swap12]
      linarith
    have h10 : (0:ℝ) < 1 - t (i - 1) := by linarith [(ht (i - 1)).2]
    nlinarith
  have hsq : 0 ≤ cr (sidePt i (t i) - hexVtx i) (innerVtx i - hexVtx i) := by
    rw [hsub2, hXsub, cr_smul_left, cr_smul_right]
    have hpos : 0 < S (hexVtx i) (hexVtx (i + 1)) (hexVtx (i + 2)) :=
      convexPos_hexagonList_cyc (by fin_cases i <;> simp only [Fin.val_add] <;> omega)
    have hsign : 0 < cr (hexVtx (i + 1) - hexVtx i) (hexVtx (i + 2) - hexVtx i) := by
      have h2 : cr (hexVtx (i + 1) - hexVtx i) (hexVtx (i + 2) - hexVtx i) =
          S (hexVtx i) (hexVtx (i + 1)) (hexVtx (i + 2)) := rfl
      rw [h2]
      linarith
    have ht0 : (0:ℝ) ≤ t i := (ht i).1
    nlinarith
  exact corner_crossing i (innerVtx i) (2/3) (by norm_num) (by norm_num)
    (innerVtx_segment i) ht hsp hsq

/-- Crossing over the chord between the two sides adjacent to corner `i`,
with `X = I (i-1)`. -/
lemma corner_crossing_B (i : Fin 6) {t : Fin 6 → ℝ} (ht : ∀ j : Fin 6, 0 ≤ t j ∧ t j < 1) :
    ∃ z : Pt, ∃ lam r : ℝ, 0 ≤ lam ∧ lam ≤ 1 ∧ 0 ≤ r ∧ r ≤ 1 ∧
      z = sidePt (i - 1) (t (i - 1)) + lam • (sidePt i (t i) - sidePt (i - 1) (t (i - 1))) ∧
      z = hexVtx i + r • (innerVtx (i - 1) - hexVtx i) := by
  have h1 : (i - 1 + 1 : Fin 6) = i := by fin_cases i <;> rfl
  have hsub1 : sidePt (i - 1) (t (i - 1)) - hexVtx i = (1 - t (i - 1)) • (hexVtx (i - 1) - hexVtx i) := by
    rw [sidePt, h1]
    module
  have hsub2 : sidePt i (t i) - hexVtx i = t i • (hexVtx (i + 1) - hexVtx i) := by
    rw [sidePt]
    module
  have hXsub : innerVtx (i - 1) - hexVtx i = (1/3 : ℝ) • (hexVtx (i - 2) - hexVtx i) := by
    rw [innerVtx_pred_diagonal2 i]
    module
  have hsp : cr (sidePt (i - 1) (t (i - 1)) - hexVtx i) (innerVtx (i - 1) - hexVtx i) ≤ 0 := by
    rw [hsub1, hXsub, cr_smul_left, cr_smul_right]
    have hpos : 0 < S (hexVtx (i - 2)) (hexVtx (i - 1)) (hexVtx i) :=
      convexPos_hexagonList_cyc (by fin_cases i <;> simp only [Fin.val_sub] <;> omega)
    have hsign : cr (hexVtx (i - 1) - hexVtx i) (hexVtx (i - 2) - hexVtx i) < 0 := by
      have h2 : cr (hexVtx (i - 1) - hexVtx i) (hexVtx (i - 2) - hexVtx i) =
          S (hexVtx i) (hexVtx (i - 1)) (hexVtx (i - 2)) := rfl
      rw [h2, S_cyclic, S_cyclic, S_swap_right]
      linarith
    have h10 : (0:ℝ) < 1 - t (i - 1) := by linarith [(ht (i - 1)).2]
    nlinarith
  have hsq : 0 ≤ cr (sidePt i (t i) - hexVtx i) (innerVtx (i - 1) - hexVtx i) := by
    rw [hsub2, hXsub, cr_smul_left, cr_smul_right]
    have hpos : 0 < S (hexVtx (i - 2)) (hexVtx i) (hexVtx (i + 1)) :=
      convexPos_hexagonList_cyc (by fin_cases i <;> simp only [Fin.val_add, Fin.val_sub] <;> omega)
    have hsign : 0 < cr (hexVtx (i + 1) - hexVtx i) (hexVtx (i - 2) - hexVtx i) := by
      have h2 : cr (hexVtx (i + 1) - hexVtx i) (hexVtx (i - 2) - hexVtx i) =
          S (hexVtx i) (hexVtx (i + 1)) (hexVtx (i - 2)) := rfl
      rw [h2, S_cyclic, S_cyclic]
      linarith
    have ht0 : (0:ℝ) ≤ t i := (ht i).1
    nlinarith
  exact corner_crossing i (innerVtx (i - 1)) (1/3) (by norm_num) (by norm_num)
    (innerVtx_pred_segment i) ht hsp hsq


/-- The two inner vertices on the diagonal from `V m` to `V (m+2)` are convex
combinations of two crossing points, one on each adjacent chord. -/
lemma innerVtx_combo (m : Fin 6) {z₁ z₂ : Pt} {r₁ r₂ : ℝ}
    (_hr₁0 : 0 ≤ r₁) (hr₁1 : r₁ ≤ 1) (_hr₂0 : 0 ≤ r₂) (hr₂1 : r₂ ≤ 1)
    (hz₁ : z₁ = hexVtx m + r₁ • (innerVtx m - hexVtx m))
    (hz₂ : z₂ = hexVtx (m + 2) + r₂ • (innerVtx (m + 1) - hexVtx (m + 2))) :
    ∃ μ μ' : ℝ, 0 ≤ μ ∧ μ ≤ 1 ∧ 0 ≤ μ' ∧ μ' ≤ 1 ∧
      innerVtx m = (1 - μ) • z₁ + μ • z₂ ∧
      innerVtx (m + 1) = (1 - μ') • z₁ + μ' • z₂ := by
  have hden : (0:ℝ) < 3 - r₁ - r₂ := by linarith
  have hI2 : innerVtx (m + 1) = hexVtx (m + 2) + (1/3 : ℝ) • (hexVtx m - hexVtx (m + 2)) := by
    have h22 : ((m + 2) - 2 : Fin 6) = m := by fin_cases m <;> rfl
    have h21 : ((m + 2) - 1 : Fin 6) = m + 1 := by fin_cases m <;> rfl
    have e := innerVtx_pred_diagonal2 (m + 2)
    rw [h22, h21] at e
    exact e
  set w := hexVtx (m + 2) - hexVtx m with hwdef
  have hI : innerVtx m = hexVtx m + (1/3 : ℝ) • w := innerVtx_diagonal m
  have hI' : innerVtx (m + 1) = hexVtx m + (2/3 : ℝ) • w := innerVtx_succ_diagonal' m
  have hz1 : z₁ = hexVtx m + (r₁ / 3) • w := by
    rw [hz₁, innerVtx_diagonal m, hwdef]
    module
  have hz2 : z₂ = hexVtx m + (1 - r₂ / 3) • w := by
    rw [hz₂, hI2, hwdef]
    module
  have hK : (1 - (1 - r₁) / (3 - r₁ - r₂)) * (r₁ / 3) +
      ((1 - r₁) / (3 - r₁ - r₂)) * (1 - r₂ / 3) = 1 / 3 := by
    field_simp
    ring
  have hK' : (1 - (2 - r₁) / (3 - r₁ - r₂)) * (r₁ / 3) +
      ((2 - r₁) / (3 - r₁ - r₂)) * (1 - r₂ / 3) = 2 / 3 := by
    field_simp
    ring
  refine ⟨(1 - r₁) / (3 - r₁ - r₂), (2 - r₁) / (3 - r₁ - r₂),
    div_nonneg (by linarith) hden.le, (div_le_one hden).2 (by linarith),
    div_nonneg (by linarith) hden.le, (div_le_one hden).2 (by linarith), ?_, ?_⟩
  · rw [hz1, hz2, hI]
    rw [show (1 - (1 - r₁) / (3 - r₁ - r₂)) • (hexVtx m + (r₁ / 3) • w) +
        ((1 - r₁) / (3 - r₁ - r₂)) • (hexVtx m + (1 - r₂ / 3) • w) =
      hexVtx m + ((1 - (1 - r₁) / (3 - r₁ - r₂)) * (r₁ / 3) +
        ((1 - r₁) / (3 - r₁ - r₂)) * (1 - r₂ / 3)) • w from by module]
    rw [hK]
  · rw [hz1, hz2, hI']
    rw [show (1 - (2 - r₁) / (3 - r₁ - r₂)) • (hexVtx m + (r₁ / 3) • w) +
        ((2 - r₁) / (3 - r₁ - r₂)) • (hexVtx m + (1 - r₂ / 3) • w) =
      hexVtx m + ((1 - (2 - r₁) / (3 - r₁ - r₂)) * (r₁ / 3) +
        ((2 - r₁) / (3 - r₁ - r₂)) * (1 - r₂ / 3)) • w from by module]
    rw [hK']


lemma S_neg_swap13 (a b c : Pt) : S c b a = -S a b c := by rw [S_cyclic, S_swap_left]

/-- Any three distinct indices of a convex-position list give a nondegenerate
triangle. -/
lemma ConvexPos.S_ne_zero {l : List Pt} (h : ConvexPos l) {i j k : ℕ}
    (hi : i < l.length) (hj : j < l.length) (hk : k < l.length)
    (hd : i ≠ j ∧ j ≠ k ∧ k ≠ i) : S (l[i]'(hi)) (l[j]'(hj)) (l[k]'(hk)) ≠ 0 := by
  rcases (by omega : (i < j ∧ j < k) ∨ (j < k ∧ k < i) ∨ (k < i ∧ i < j) ∨
      (k < j ∧ j < i) ∨ (j < i ∧ i < k) ∨ (i < k ∧ k < j)) with hord|hord|hord|hord|hord|hord
  · exact (h.cyc hi hj hk (Or.inl hord)).ne'
  · exact (h.cyc hi hj hk (Or.inr (Or.inl hord))).ne'
  · exact (h.cyc hi hj hk (Or.inr (Or.inr hord))).ne'
  · have hpos : 0 < S (l[k]'(hk)) (l[j]'(hj)) (l[i]'(hi)) := h.cyc hk hj hi (Or.inl hord)
    rw [S_neg_swap13]
    linarith
  · have hpos : 0 < S (l[j]'(hj)) (l[i]'(hi)) (l[k]'(hk)) := h.cyc hj hi hk (Or.inl hord)
    rw [S_neg_swap12]
    linarith
  · have hpos : 0 < S (l[i]'(hi)) (l[k]'(hk)) (l[j]'(hj)) := h.cyc hi hk hj (Or.inl hord)
    rw [S_swap_right]
    linarith

/-- Any two distinct indices of a convex-position list give distinct points. -/
lemma ConvexPos.ne {l : List Pt} (h : ConvexPos l) {i j k : ℕ}
    (hi : i < l.length) (hj : j < l.length) (hk : k < l.length)
    (hd : i ≠ j ∧ j ≠ k ∧ k ≠ i) : l[i]'(hi) ≠ l[j]'(hj) := by
  intro heq
  have h2 : S (l[i]'(hi)) (l[j]'(hj)) (l[k]'(hk)) = 0 := by rw [heq, S_self_left]
  exact h.S_ne_zero hi hj hk hd h2

lemma mod_succ_ne (n j : ℕ) (h3 : 3 ≤ n) (hj : j < n) :
    j ≠ (j + 1) % n ∧ (j + 1) % n ≠ (j + 2) % n ∧ (j + 2) % n ≠ j := by
  by_cases h1 : j + 2 < n
  · rw [Nat.mod_eq_of_lt (by omega : j + 1 < n), Nat.mod_eq_of_lt h1]
    omega
  · have hn : j + 1 = n ∨ j + 2 = n := by omega
    rcases hn with hn | hn
    · rw [show (j + 1) % n = 0 from by rw [hn, Nat.mod_self],
        show (j + 2) % n = 1 from by rw [show j + 2 = n + 1 from by omega, Nat.add_comm n 1,
          Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : 1 < n)]]
      omega
    · rw [show (j + 1) % n = n - 1 from by
        rw [Nat.mod_eq_of_lt (by omega : j + 1 < n), show j + 1 = n - 1 from by omega],
        show (j + 2) % n = 0 from by rw [hn, Nat.mod_self]]
      omega

/-- Points of side `d` of the hexagon lie strictly to the left of edge `c`,
when `d` is not `c` or `c+1`. -/
lemma S_edge_pos (c d : Fin 6) (hd : d ≠ c ∧ d ≠ c + 1) :
    0 < S (hexVtx c) (hexVtx (c + 1)) (hexVtx d) :=
  convexPos_hexagonList_cyc (by fin_cases c <;> fin_cases d <;>
    simp at hd ⊢)

/-- A point of a segment whose endpoints lie strictly to the left of a
directed edge also lies strictly to the left of that edge. -/
lemma S_side_pos' {x a b d₁ d₂ : Pt} (hx : onSeg x d₁ d₂)
    (hp : 0 < S a b d₁) (hq : 0 < S a b d₂) : 0 < S a b x := by
  obtain ⟨t, ht0, ht1, rfl⟩ := hx
  rw [show d₁ + t • (d₂ - d₁) = (1 - t) • d₁ + t • d₂ from by module, S_convexCombo₃]
  by_cases ht : t = 1
  · rw [ht]
    nlinarith
  · have hpos1 : 0 < (1 - t) * S a b d₁ := mul_pos (sub_pos.2 (lt_of_le_of_ne ht1 ht)) hp
    have hpos2 : 0 ≤ t * S a b d₂ := mul_nonneg ht0 hq.le
    nlinarith

/-- A point on a segment is collinear with its endpoints. -/
lemma S_side_zero {x a b : Pt} (hx : onSeg x a b) : S a b x = 0 := by
  obtain ⟨t, ht0, ht1, rfl⟩ := hx
  rw [show a + t • (b - a) = (1 - t) • a + t • b from by
    module, S_convexCombo₃, S_self_mid, S_self_right]
  ring

/-- The only common point of two adjacent sides is the shared corner. -/
lemma corner_only {x : Pt} {c : Fin 6}
    (h1 : onSeg x (hexVtx c) (hexVtx (c + 1)))
    (h2 : onSeg x (hexVtx (c + 1)) (hexVtx (c + 2))) :
    x = hexVtx (c + 1) := by
  obtain ⟨t1, ht10, ht11, hx1⟩ := h1
  have hpos : 0 < S (hexVtx c) (hexVtx (c + 1)) (hexVtx (c + 2)) :=
    convexPos_hexagonList_cyc (by fin_cases c <;> simp only [Fin.val_add] <;> omega)
  have hS : S (hexVtx (c + 1)) (hexVtx (c + 2)) x = 0 := S_side_zero h2
  rw [hx1, show hexVtx c + t1 • (hexVtx (c + 1) - hexVtx c) =
    (1 - t1) • hexVtx c + t1 • hexVtx (c + 1) from by module, S_convexCombo₃] at hS
  have hS1 : S (hexVtx (c + 1)) (hexVtx (c + 2)) (hexVtx c) =
      S (hexVtx c) (hexVtx (c + 1)) (hexVtx (c + 2)) := by
    rw [S_cyclic, S_cyclic]
  have hS2 : S (hexVtx (c + 1)) (hexVtx (c + 2)) (hexVtx (c + 1)) = 0 := S_self_mid _ _
  rw [hS1, hS2] at hS
  have ht1 : t1 = 1 := by
    have hSn : S (hexVtx c) (hexVtx (c + 1)) (hexVtx (c + 2)) ≠ 0 := hpos.ne'
    have hzero : (1 - t1) * S (hexVtx c) (hexVtx (c + 1)) (hexVtx (c + 2)) = 0 := by
      linarith
    rcases mul_eq_zero.1 hzero with h' | h'
    · linarith
    · exact absurd h' hSn
  rw [ht1] at hx1
  rw [hx1]
  simp [one_smul]


/-- The two chosen vertices on the same side are distinct. -/
lemma sel_inj {l : List Pt} (_hcp : ConvexPos l) {j : Fin 6 → ℕ}
    (hj : ∀ c, j c < l.length)
    (hjsel : ∀ c, onSeg (l[j c]'(hj c)) (hexVtx c) (hexVtx (c + 1)))
    (hne : ∀ c, l[j c]'(hj c) ≠ hexVtx (c + 1)) {c₁ c₂ : Fin 6} (hc : c₁ ≠ c₂) :
    j c₁ ≠ j c₂ := by
  intro heq
  have hp1 := hjsel c₁
  have hp2 := hjsel c₂
  have hpt : l[j c₁]'(hj c₁) = l[j c₂]'(hj c₂) := getElem_congr_idx (hj c₁) (hj c₂) heq
  rw [← hpt] at hp2
  fin_cases c₁ <;> fin_cases c₂ <;> simp at hc
  all_goals first
    | exact (hne _) (corner_only hp1 hp2)
    | exact (hne _) (by
        have h3 := corner_only hp2 hp1
        rw [hpt] at h3
        exact h3)
    | exact absurd (S_side_zero hp1) (by
        apply LT.lt.ne'
        exact S_side_pos' hp2 (S_edge_pos _ _ ⟨by decide, by decide⟩)
          (S_edge_pos _ _ ⟨by decide, by decide⟩))

/-- Choose one vertex on each side of the hexagon (not equal to the forward
corner). -/
lemma choose_vertices {l : List Pt} (h6 : 6 ≤ l.length) (hcp : ConvexPos l)
    (hside : ∀ c : Fin 6, SidePair l c) :
    ∃ j : Fin 6 → ℕ, ∃ hj : ∀ c, j c < l.length,
      (∀ c, onSeg (l[j c]'(hj c)) (hexVtx c) (hexVtx (c + 1))) ∧
      (∀ c, l[j c]'(hj c) ≠ hexVtx (c + 1)) ∧
      (∀ c₁ c₂ : Fin 6, c₁ ≠ c₂ → j c₁ ≠ j c₂) := by
  have hsel : ∀ c : Fin 6, ∃ j : ℕ, ∃ hj : j < l.length,
      onSeg (l[j]'(hj)) (hexVtx c) (hexVtx (c + 1)) ∧ l[j]'(hj) ≠ hexVtx (c + 1) := by
    intro c
    obtain ⟨j, hj, h1, h2⟩ := hside c
    by_cases hx : l[j]'(hj) = hexVtx (c + 1)
    · refine ⟨(j + 1) % l.length, Nat.mod_lt _ (by omega), h2, fun heq => ?_⟩
      have hne2 : l[j]'(hj) ≠ l[(j + 1) % l.length]'(Nat.mod_lt _ (by omega)) := by
        have h3 := mod_succ_ne l.length j (by omega) hj
        exact hcp.ne hj (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega)) h3
      exact hne2 (by rw [hx, heq])
    · exact ⟨j, hj, h1, hx⟩
  choose j hj hjsel hne using hsel
  exact ⟨j, hj, hjsel, hne, fun c₁ c₂ hc => sel_inj hcp hj hjsel hne hc⟩

/-- Each chosen vertex is a `sidePt` with parameter in `[0, 1)`. -/
lemma choose_params {l : List Pt} {j : Fin 6 → ℕ} {hj : ∀ c, j c < l.length}
    (hjsel : ∀ c, onSeg (l[j c]'(hj c)) (hexVtx c) (hexVtx (c + 1)))
    (hne : ∀ c, l[j c]'(hj c) ≠ hexVtx (c + 1)) :
    ∃ t : Fin 6 → ℝ, (∀ c, 0 ≤ t c ∧ t c < 1) ∧
      ∀ c, l[j c]'(hj c) = sidePt c (t c) := by
  have hpt : ∀ c : Fin 6, ∃ t : ℝ, 0 ≤ t ∧ t < 1 ∧ l[j c]'(hj c) = sidePt c t := by
    intro c
    obtain ⟨t, ht0, ht1, heq⟩ := hjsel c
    have ht1' : t < 1 := by
      rcases ht1.eq_or_lt with h | h
      · exfalso
        apply hne c
        rw [heq, h]
        module
      · exact h
    exact ⟨t, ht0, ht1', heq⟩
  choose t ht heq using hpt
  exact ⟨t, fun c => ⟨ht c, (heq c).1⟩, fun c => (heq c).2⟩


/-! ### Sorting the six chosen vertices and the extraction bound -/

/-- Package the vertex selection. -/
lemma selection_exists {l : List Pt} (h6 : 6 ≤ l.length) (hcp : ConvexPos l)
    (hside : ∀ c : Fin 6, SidePair l c) :
    ∃ j : Fin 6 → ℕ, ∃ t : Fin 6 → ℝ, ∃ hj : ∀ c, j c < l.length,
      (∀ c, 0 ≤ t c ∧ t c < 1) ∧ (∀ c, l[j c]'(hj c) = sidePt c (t c)) ∧
      Function.Injective j := by
  obtain ⟨j, hj, hjsel, hne, hinj⟩ := choose_vertices h6 hcp hside
  obtain ⟨t, ht, heq⟩ := choose_params hjsel hne
  exact ⟨j, t, hj, ht, heq, fun a b hab => by by_contra hne2; exact hinj a b hne2 hab⟩

lemma List.ne_nil_of_length_pos {α : Type*} {l : List α} (h : 0 < l.length) : l ≠ [] := by
  intro hcon
  rw [hcon] at h
  simp at h

lemma take_ne_nil {α : Type*} (l : List α) (k : ℕ) (hk : 0 < k) (hk2 : k ≤ l.length) :
    l.take k ≠ [] := by
  show ¬(l.take k = [])
  rw [List.take_eq_nil_iff]
  push Not
  exact ⟨by omega, List.ne_nil_of_length_pos (by omega : 0 < l.length)⟩

lemma drop_ne_nil {α : Type*} (l : List α) (k : ℕ) (hk : k < l.length) : l.drop k ≠ [] := by
  show ¬(l.drop k = [])
  rw [List.drop_eq_nil_iff]
  omega

lemma fanSum_singleton (x y : Pt) : fanSum x [y] = 0 := by simp [fanSum]

lemma zipWith_append_left (f : Pt → Pt → ℝ) (P Q : List Pt) (hP : P ≠ []) (hQ : Q ≠ []) :
    (P ++ Q).zipWith f (P.tail ++ Q) = P.zipWith f (P.tail ++ [Q.head hQ]) ++ Q.zipWith f Q.tail := by
  induction P with
  | nil => exact absurd rfl hP
  | cons a rest ih =>
    cases rest with
    | nil =>
      cases Q with
      | nil => exact absurd rfl hQ
      | cons b rest => simp
    | cons b rest =>
      have hne : (b :: rest) ≠ [] := by simp
      simp only [List.cons_append, List.tail_cons, List.zipWith_cons_cons]
      simp only [List.cons_append, List.tail_cons] at ih
      rw [ih hne]

lemma fanSum_append (x : Pt) (P Q : List Pt) (hP : P ≠ []) (hQ : Q ≠ []) :
    fanSum x (P ++ Q) = fanSum x P + S x (P.getLast hP) (Q.head hQ) + fanSum x Q := by
  have htail : (P ++ Q).tail = P.tail ++ Q := by
    cases P with
    | nil => exact absurd rfl hP
    | cons a rest => simp
  rw [fanSum, fanSum, fanSum, htail, zipWith_append_left _ P Q hP hQ,
    zipWith_tail_append_singleton (fun a b => S x a b) (Q.head hQ) P hP]
  simp
  ac_rfl

lemma fanSum_nonneg (x : Pt) (l : List Pt)
    (hx : ∀ i : ℕ, ∀ (h1 : 1 ≤ i) (h2 : i < l.length),
      0 ≤ S x (l[i - 1]'(by omega)) (l[i]'(h2))) :
    0 ≤ fanSum x l := by
  induction l with
  | nil => simp [fanSum]
  | cons a rest ih =>
    cases rest with
    | nil => simp [fanSum]
    | cons b rest =>
      rw [fanSum_cons_cons]
      have h1 := hx 1 (le_refl 1) (by simp)
      have h2 := ih (by
        intro i h1i h2i
        have e := hx (i + 1) (by omega) (by nth_rewrite 1 [List.length_cons]; omega)
        have e2 : (a :: b :: rest)[i + 1 - 1]'(by nth_rewrite 1 [List.length_cons]; omega) =
            (a :: b :: rest)[i - 1 + 1]'(by nth_rewrite 1 [List.length_cons]; omega) :=
          getElem_congr_idx _ _ (by omega)
        rw [e2] at e
        simpa [List.getElem_cons_succ] using e)
      simp at h1
      linarith

lemma fanSum_le_of_take (x : Pt) (l : List Pt)
    (hx : ∀ i : ℕ, ∀ (h1 : 1 ≤ i) (h2 : i < l.length),
      0 ≤ S x (l[i - 1]'(by omega)) (l[i]'(h2)))
    (k : ℕ) : fanSum x (l.take k) ≤ fanSum x l := by
  by_cases hk : k < l.length
  · rcases (by omega : k = 0 ∨ 1 ≤ k) with rfl | hk1
    · rw [List.take_zero, show fanSum x [] = 0 from by simp [fanSum]]
      exact fanSum_nonneg x l hx
    · have hne1 : l.take k ≠ [] := take_ne_nil l k hk1 hk.le
      have hne2 : l.drop k ≠ [] := drop_ne_nil l k hk
      have hfa := fanSum_append x (l.take k) (l.drop k) hne1 hne2
      have e1 : (l.take k).getLast hne1 = l[k - 1]'(by omega) := by
        rw [List.getLast_take, List.getElem?_eq_getElem (h := by omega)]
        exact getElem_congr_idx _ _ rfl
      have e2 : (l.drop k).head hne2 = l[k]'(hk) := by
        rw [List.head_drop]
      rw [show fanSum x l = fanSum x (l.take k ++ l.drop k) from by rw [List.take_append_drop],
        hfa, e1, e2]
      have h2 : 0 ≤ fanSum x (l.drop k) := by
        apply fanSum_nonneg
        intro i h1i h2i
        have h2i' := h2i
        simp only [List.length_drop] at h2i'
        have e := hx (k + i) (by omega) (by omega)
        have e1 : (l.drop k)[i - 1]'(by omega) = l[k + i - 1]'(by omega) := by
          rw [List.getElem_drop]
          exact getElem_congr_idx _ _ (by omega)
        have e2 : (l.drop k)[i]'(by simpa using h2i') = l[k + i]'(by omega) := by
          rw [List.getElem_drop]
        rw [e1, e2]
        exact e
      have h1 := hx k hk1 hk
      linarith [h2, h1]
  · rw [List.take_of_length_le (by omega)]

/-- The arc bound: the fan triangle over a chord is bounded by the fan sum
over the chain of edges below it. -/
lemma fan_arc_bound {l : List Pt} (h : ConvexPos l) {a b : ℕ}
    (ha : 1 ≤ a) (hb : a < b) (hbn : b < l.length) :
    S (l[0]'(by omega)) (l[a]'(by omega)) (l[b]'(hbn)) ≤
      fanSum (l[0]'(by omega)) ((l.drop a).take (b - a + 1)) := by
  induction b, hb using Nat.le_induction with
  | base =>
    -- b = a + 1: the chain is [l[a], l[a+1]]
    have e : (l.drop a).take (a + 1 - a + 1) = [l[a]'(by omega), l[(a + 1)]'(by omega)] := by
      rw [show a + 1 - a + 1 = 2 from by omega, show (2 : ℕ) = 1 + 1 from rfl, List.take_add,
        List.take_one, List.head?_drop, List.getElem?_eq_getElem (h := by omega),
        List.drop_drop, List.take_one, List.head?_drop, List.getElem?_eq_getElem (h := by omega)]
      simp
    rw [e]
    simp [fanSum]
  | succ b hb2 ih =>
    have e : (l.drop a).take (b + 1 - a + 1) =
        (l.drop a).take (b - a + 1) ++ [l[(b + 1)]'(by omega)] := by
      rw [show b + 1 - a + 1 = (b - a + 1) + 1 from by omega, List.take_add,
        List.drop_drop, show a + (b - a + 1) = b + 1 from by omega, List.take_one,
        List.head?_drop, List.getElem?_eq_getElem (h := by omega)]
      simp
    have elast : ((l.drop a).take (b - a + 1)).getLast
        (take_ne_nil _ _ (by omega) (by simp only [List.length_drop]; omega)) =
        l[b]'(by omega) := by
      rw [List.getLast_take, List.getElem?_drop, List.getElem?_eq_getElem (h := by omega),
        Option.getD_some]
      exact getElem_congr_idx _ _ (by omega)
    rw [e, fanSum_append (l[0]'(by omega)) ((l.drop a).take (b - a + 1)) [l[(b + 1)]'(by omega)]
      (take_ne_nil _ _ (by omega) (by simp only [List.length_drop]; omega)) (by simp),
      fanSum_singleton, elast, List.head_cons]
    have h2 : S (l[0]'(by omega)) (l[a]'(by omega)) (l[(b + 1)]'(by omega)) =
        S (l[0]'(by omega)) (l[a]'(by omega)) (l[b]'(by omega)) +
        S (l[0]'(by omega)) (l[b]'(by omega)) (l[(b + 1)]'(by omega)) -
        S (l[a]'(by omega)) (l[b]'(by omega)) (l[(b + 1)]'(by omega)) := by
      simp only [S, cr, WithLp.ofLp_sub, Pi.sub_apply]
      ring
    have h3 : 0 < S (l[a]'(by omega)) (l[b]'(by omega)) (l[(b + 1)]'(by omega)) :=
      h.cyc (by omega) (by omega) (by omega) (by omega)
    have h4 := ih (by omega)
    linarith

/-- Taking `k + 1` elements of a dropped list peels off the head element. -/
lemma take_drop_succ (l : List Pt) (b k : ℕ) (hb : b < l.length) :
    (l.drop b).take (k + 1) = l[b]'hb :: (l.drop (b + 1)).take k := by
  rw [List.drop_eq_getElem_cons hb, show k + 1 = 1 + k from by omega, List.take_add,
    List.drop_one, List.tail_cons, List.take_one, List.head?_cons]
  rfl

/-- The last element of a nonempty `take` of a `drop`. -/
lemma getLast_take_drop (l : List Pt) (a n : ℕ) (hn : 1 ≤ n) (h : a + n - 1 < l.length) :
    ((l.drop a).take n).getLast (take_ne_nil _ _ hn (by simp only [List.length_drop]; omega)) =
      l[a + n - 1]'(h) := by
  rw [List.getLast_take, List.getElem?_drop, List.getElem?_eq_getElem (h := by omega),
    Option.getD_some]
  exact getElem_congr_idx _ _ (by omega)

/-- Chained fan sums decompose over chained index intervals. -/
lemma fanSum_chain_add (x : Pt) (l : List Pt) (a b c : ℕ) (hab : a ≤ b) (hbc : b ≤ c)
    (hb : b < l.length) (hc : c < l.length) :
    fanSum x ((l.drop a).take (c - a + 1)) =
      fanSum x ((l.drop a).take (b - a + 1)) + fanSum x ((l.drop b).take (c - b + 1)) := by
  rcases (by omega : b = c ∨ b < c) with rfl | hbc'
  · have hz : fanSum x ((l.drop b).take (b - b + 1)) = 0 := by
      rw [show b - b + 1 = 1 from by omega, List.take_one, List.head?_drop,
        List.getElem?_eq_getElem (h := hb)]
      exact fanSum_singleton x (l[b]'hb)
    rw [hz, add_zero]
  · have e1 : (l.drop a).take (c - a + 1) =
        (l.drop a).take (b - a + 1) ++ (l.drop (b + 1)).take (c - b) := by
      rw [show c - a + 1 = (b - a + 1) + (c - b) from by omega, List.take_add,
        List.drop_drop, show a + (b - a + 1) = b + 1 from by omega]
    have eB : (l.drop (b + 1)).take (c - b) =
        l[(b + 1)]'(by omega) :: (l.drop (b + 2)).take (c - b - 1) := by
      rw [show c - b = (c - b - 1) + 1 from by omega]
      exact take_drop_succ l (b + 1) (c - b - 1) (by omega)
    have e3 : (l.drop b).take (c - b + 1) = l[b]'hb :: (l.drop (b + 1)).take (c - b) :=
      take_drop_succ l b (c - b) hb
    rw [e1, e3, eB, fanSum_cons_cons,
      fanSum_append x ((l.drop a).take (b - a + 1)) _
        (take_ne_nil _ _ (by omega) (by simp only [List.length_drop]; omega)) (by simp),
      List.head_cons, getLast_take_drop l a (b - a + 1) (by omega) (by omega),
      getElem_congr_idx (by omega : a + (b - a + 1) - 1 < l.length) hb (by omega)]
    ac_rfl

/-- Dropping an initial segment can only shrink the fan sum when all
consecutive fan terms are nonnegative. -/
lemma fanSum_drop_le (x : Pt) (l : List Pt)
    (hx : ∀ i : ℕ, ∀ (h1 : 1 ≤ i) (h2 : i < l.length),
      0 ≤ S x (l[i - 1]'(by omega)) (l[i]'(h2)))
    (j : ℕ) : fanSum x (l.drop j) ≤ fanSum x l := by
  by_cases hj : j < l.length
  · rcases (by omega : j = 0 ∨ 1 ≤ j) with rfl | hj1
    · rw [List.drop_zero]
    · have hne1 : l.take j ≠ [] := take_ne_nil l j hj1 hj.le
      have hne2 : l.drop j ≠ [] := drop_ne_nil l j hj
      have hfa := fanSum_append x (l.take j) (l.drop j) hne1 hne2
      have e1 : (l.take j).getLast hne1 = l[j - 1]'(by omega) := by
        rw [List.getLast_take, List.getElem?_eq_getElem (h := by omega)]
        exact getElem_congr_idx _ _ rfl
      have e2 : (l.drop j).head hne2 = l[j]'(hj) := by
        rw [List.head_drop]
      rw [show fanSum x l = fanSum x (l.take j ++ l.drop j) from by rw [List.take_append_drop],
        hfa, e1, e2]
      have h1 : 0 ≤ fanSum x (l.take j) := by
        apply fanSum_nonneg
        intro i h1i h2i
        have h2i' := h2i
        simp only [List.length_take] at h2i'
        have e := hx i h1i (by omega)
        rw [List.getElem_take, List.getElem_take]
        exact e
      have h2 := hx j hj1 hj
      linarith [h1, h2]
  · rw [List.drop_of_length_le (by omega)]
    rw [show fanSum x [] = 0 from by simp [fanSum]]
    exact fanSum_nonneg x l hx

/-- A fan sum over a middle interval is bounded by the fan sum over the whole
list when all consecutive fan terms are nonnegative. -/
lemma fanSum_drop_take_le (x : Pt) (l : List Pt)
    (hx : ∀ i : ℕ, ∀ (h1 : 1 ≤ i) (h2 : i < l.length),
      0 ≤ S x (l[i - 1]'(by omega)) (l[i]'(h2)))
    (j m : ℕ) : fanSum x ((l.drop j).take m) ≤ fanSum x l := by
  rcases (by omega : m = 0 ∨ 1 ≤ m) with rfl | hm1
  · rw [List.take_zero, show fanSum x [] = 0 from by simp [fanSum]]
    exact fanSum_nonneg x l hx
  · have e1 : fanSum x ((l.drop j).take m) ≤ fanSum x (l.drop j) := by
      apply fanSum_le_of_take
      intro i h1i h2i
      have h2i' := h2i
      simp only [List.length_drop] at h2i'
      have e := hx (j + i) (by omega) (by omega)
      have e1 : (l.drop j)[i - 1]'(by omega) = l[j + i - 1]'(by omega) := by
        rw [List.getElem_drop]
        exact getElem_congr_idx _ _ (by omega)
      have e2 : (l.drop j)[i]'(h2i) = l[j + i]'(by omega) := by
        rw [List.getElem_drop]
      rw [e1, e2]
      exact e
    exact le_trans e1 (fanSum_drop_le x l hx j)

/-- The shoelace sum of a polygon formed by the first vertex plus five
cyclically later vertices is at most the shoelace sum of the whole polygon. -/
lemma extraction_bound {l : List Pt} (h : ConvexPos l)
    (d : Fin 6 → ℕ) (hd0 : d 0 = 0) (hd_mono : ∀ a b : Fin 6, a < b → d a < d b)
    (hd_lt : ∀ k : Fin 6, d k < l.length) :
    shoelace ((l[d 0]'(hd_lt 0)) :: [(l[d 1]'(hd_lt 1)), (l[d 2]'(hd_lt 2)), (l[d 3]'(hd_lt 3)),
      (l[d 4]'(hd_lt 4)), (l[d 5]'(hd_lt 5))]) ≤ shoelace l := by
  have h01 : d 0 < d 1 := hd_mono 0 1 (by decide)
  have h12 : d 1 < d 2 := hd_mono 1 2 (by decide)
  have h23 : d 2 < d 3 := hd_mono 2 3 (by decide)
  have h34 : d 3 < d 4 := hd_mono 3 4 (by decide)
  have h45 : d 4 < d 5 := hd_mono 4 5 (by decide)
  have h1 : 1 ≤ d 1 := by omega
  have h5 : d 5 < l.length := hd_lt 5
  have hn : 0 < l.length := by have := hd_lt 0; omega
  rw [shoelace_eq_fanSum _ _ (by simp)]
  have apex : l[d 0]'(hd_lt 0) = l[0]'(hn) := getElem_congr_idx _ _ hd0
  have hfan : fanSum (l[d 0]'(hd_lt 0)) [(l[d 1]'(hd_lt 1)), (l[d 2]'(hd_lt 2)), (l[d 3]'(hd_lt 3)),
      (l[d 4]'(hd_lt 4)), (l[d 5]'(hd_lt 5))] =
      S (l[d 0]'(hd_lt 0)) (l[d 1]'(hd_lt 1)) (l[d 2]'(hd_lt 2)) +
      S (l[d 0]'(hd_lt 0)) (l[d 2]'(hd_lt 2)) (l[d 3]'(hd_lt 3)) +
      S (l[d 0]'(hd_lt 0)) (l[d 3]'(hd_lt 3)) (l[d 4]'(hd_lt 4)) +
      S (l[d 0]'(hd_lt 0)) (l[d 4]'(hd_lt 4)) (l[d 5]'(hd_lt 5)) := by
    rw [fanSum_cons_cons, fanSum_cons_cons, fanSum_cons_cons, fanSum_cons_cons,
      fanSum_singleton]
    ring
  rw [hfan, apex]
  have e1 : S (l[0]'(hn)) (l[d 1]'(hd_lt 1)) (l[d 2]'(hd_lt 2)) ≤
      fanSum (l[0]'(hn)) ((l.drop (d 1)).take (d 2 - d 1 + 1)) :=
    fan_arc_bound h h1 h12 (hd_lt 2)
  have e2 : S (l[0]'(hn)) (l[d 2]'(hd_lt 2)) (l[d 3]'(hd_lt 3)) ≤
      fanSum (l[0]'(hn)) ((l.drop (d 2)).take (d 3 - d 2 + 1)) :=
    fan_arc_bound h (by omega) h23 (hd_lt 3)
  have e3 : S (l[0]'(hn)) (l[d 3]'(hd_lt 3)) (l[d 4]'(hd_lt 4)) ≤
      fanSum (l[0]'(hn)) ((l.drop (d 3)).take (d 4 - d 3 + 1)) :=
    fan_arc_bound h (by omega) h34 (hd_lt 4)
  have e4 : S (l[0]'(hn)) (l[d 4]'(hd_lt 4)) (l[d 5]'(hd_lt 5)) ≤
      fanSum (l[0]'(hn)) ((l.drop (d 4)).take (d 5 - d 4 + 1)) :=
    fan_arc_bound h (by omega) h45 (hd_lt 5)
  have g1 := fanSum_chain_add (l[0]'(hn)) l (d 1) (d 2) (d 3) (by omega) (by omega)
    (hd_lt 2) (hd_lt 3)
  have g2 := fanSum_chain_add (l[0]'(hn)) l (d 1) (d 3) (d 4) (by omega) (by omega)
    (hd_lt 3) (hd_lt 4)
  have g3 := fanSum_chain_add (l[0]'(hn)) l (d 1) (d 4) (d 5) (by omega) (by omega)
    (hd_lt 4) (hd_lt 5)
  have hb : fanSum (l[0]'(hn)) (((l.drop 1).drop (d 1 - 1)).take (d 5 - d 1 + 1)) ≤
      fanSum (l[0]'(hn)) (l.drop 1) := by
    apply fanSum_drop_take_le
    intro i hi1 hi2
    have hi2' := hi2
    simp only [List.length_drop] at hi2'
    have hcyc := (h.cyc (by omega : 0 < l.length) (by omega : i < l.length)
      (by omega : i + 1 < l.length) (Or.inl ⟨by omega, by omega⟩)).le
    have e1 : (l.drop 1)[i - 1]'(by omega) = l[i]'(by omega) := by
      rw [List.getElem_drop]
      exact getElem_congr_idx _ _ (by omega)
    have e2 : (l.drop 1)[i]'(hi2) = l[i + 1]'(by omega) := by
      rw [List.getElem_drop]
      exact getElem_congr_idx _ _ (by omega)
    rw [e1, e2]
    exact hcyc
  have hdrop : ((l.drop 1).drop (d 1 - 1)).take (d 5 - d 1 + 1) =
      (l.drop (d 1)).take (d 5 - d 1 + 1) := by
    rw [List.drop_drop, show 1 + (d 1 - 1) = d 1 from by omega]
  rw [hdrop] at hb
  have hshoe : shoelace l = fanSum (l[0]'(hn)) (l.drop 1) := by
    conv_lhs => rw [show l = (l[0]'(hn)) :: (l.drop 1) from by
      cases l with
      | nil => simp at hn
      | cons x xs => rfl]
    rw [shoelace_eq_fanSum _ _ (drop_ne_nil l 1 (by omega))]
  rw [hshoe]
  linarith

lemma S_sidePt_dent_nonneg_0 {t : Fin 6 → ℝ} (ht : ∀ i : Fin 6, 0 ≤ t i ∧ t i < 1) :
    0 ≤ S (sidePt 0 (t 0)) (sidePt 1 (t 1)) (innerVtx 0) := by
  obtain ⟨h00, h01⟩ := ht 0
  obtain ⟨h10, h11⟩ := ht 1
  have hEq : S (sidePt 0 (t 0)) (sidePt 1 (t 1)) (innerVtx 0) =
      scale ^ 2 * (Real.sqrt 3 / 2) * (((1 - t 0) * (1 - t 1) + 2 * t 0 * t 1) / 3) := by
    expandS
  have hs3 : (0:ℝ) < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have e1 : (0:ℝ) ≤ (1 - t 0) * (1 - t 1) :=
    mul_nonneg (sub_nonneg.2 h01.le) (sub_nonneg.2 h11.le)
  have e2 : (0:ℝ) ≤ 2 * t 0 * t 1 := mul_nonneg (mul_nonneg (by norm_num) h00) h10
  rw [hEq]
  exact mul_nonneg (mul_nonneg (pow_pos scale_pos 2).le (half_pos hs3).le) (by linarith)

lemma S_sidePt_dent_nonneg_1 {t : Fin 6 → ℝ} (ht : ∀ i : Fin 6, 0 ≤ t i ∧ t i < 1) :
    0 ≤ S (sidePt 1 (t 1)) (sidePt 2 (t 2)) (innerVtx 1) := by
  obtain ⟨h10, h11⟩ := ht 1
  obtain ⟨h20, h21⟩ := ht 2
  have hEq : S (sidePt 1 (t 1)) (sidePt 2 (t 2)) (innerVtx 1) =
      scale ^ 2 * (Real.sqrt 3 / 2) * (((1 - t 1) * (1 - t 2) + 2 * t 1 * t 2) / 3) := by
    expandS
  have hs3 : (0:ℝ) < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have e1 : (0:ℝ) ≤ (1 - t 1) * (1 - t 2) :=
    mul_nonneg (sub_nonneg.2 h11.le) (sub_nonneg.2 h21.le)
  have e2 : (0:ℝ) ≤ 2 * t 1 * t 2 := mul_nonneg (mul_nonneg (by norm_num) h10) h20
  rw [hEq]
  exact mul_nonneg (mul_nonneg (pow_pos scale_pos 2).le (half_pos hs3).le) (by linarith)

lemma S_sidePt_dent_nonneg_2 {t : Fin 6 → ℝ} (ht : ∀ i : Fin 6, 0 ≤ t i ∧ t i < 1) :
    0 ≤ S (sidePt 2 (t 2)) (sidePt 3 (t 3)) (innerVtx 2) := by
  obtain ⟨h20, h21⟩ := ht 2
  obtain ⟨h30, h31⟩ := ht 3
  have hEq : S (sidePt 2 (t 2)) (sidePt 3 (t 3)) (innerVtx 2) =
      scale ^ 2 * (Real.sqrt 3 / 2) * (((1 - t 2) * (1 - t 3) + 2 * t 2 * t 3) / 3) := by
    expandS
  have hs3 : (0:ℝ) < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have e1 : (0:ℝ) ≤ (1 - t 2) * (1 - t 3) :=
    mul_nonneg (sub_nonneg.2 h21.le) (sub_nonneg.2 h31.le)
  have e2 : (0:ℝ) ≤ 2 * t 2 * t 3 := mul_nonneg (mul_nonneg (by norm_num) h20) h30
  rw [hEq]
  exact mul_nonneg (mul_nonneg (pow_pos scale_pos 2).le (half_pos hs3).le) (by linarith)

lemma S_sidePt_dent_nonneg_3 {t : Fin 6 → ℝ} (ht : ∀ i : Fin 6, 0 ≤ t i ∧ t i < 1) :
    0 ≤ S (sidePt 3 (t 3)) (sidePt 4 (t 4)) (innerVtx 3) := by
  obtain ⟨h30, h31⟩ := ht 3
  obtain ⟨h40, h41⟩ := ht 4
  have hEq : S (sidePt 3 (t 3)) (sidePt 4 (t 4)) (innerVtx 3) =
      scale ^ 2 * (Real.sqrt 3 / 2) * (((1 - t 3) * (1 - t 4) + 2 * t 3 * t 4) / 3) := by
    expandS
  have hs3 : (0:ℝ) < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have e1 : (0:ℝ) ≤ (1 - t 3) * (1 - t 4) :=
    mul_nonneg (sub_nonneg.2 h31.le) (sub_nonneg.2 h41.le)
  have e2 : (0:ℝ) ≤ 2 * t 3 * t 4 := mul_nonneg (mul_nonneg (by norm_num) h30) h40
  rw [hEq]
  exact mul_nonneg (mul_nonneg (pow_pos scale_pos 2).le (half_pos hs3).le) (by linarith)

lemma S_sidePt_dent_nonneg_4 {t : Fin 6 → ℝ} (ht : ∀ i : Fin 6, 0 ≤ t i ∧ t i < 1) :
    0 ≤ S (sidePt 4 (t 4)) (sidePt 5 (t 5)) (innerVtx 4) := by
  obtain ⟨h40, h41⟩ := ht 4
  obtain ⟨h50, h51⟩ := ht 5
  have hEq : S (sidePt 4 (t 4)) (sidePt 5 (t 5)) (innerVtx 4) =
      scale ^ 2 * (Real.sqrt 3 / 2) * (((1 - t 4) * (1 - t 5) + 2 * t 4 * t 5) / 3) := by
    expandS
  have hs3 : (0:ℝ) < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have e1 : (0:ℝ) ≤ (1 - t 4) * (1 - t 5) :=
    mul_nonneg (sub_nonneg.2 h41.le) (sub_nonneg.2 h51.le)
  have e2 : (0:ℝ) ≤ 2 * t 4 * t 5 := mul_nonneg (mul_nonneg (by norm_num) h40) h50
  rw [hEq]
  exact mul_nonneg (mul_nonneg (pow_pos scale_pos 2).le (half_pos hs3).le) (by linarith)

lemma S_sidePt_dent_nonneg_5 {t : Fin 6 → ℝ} (ht : ∀ i : Fin 6, 0 ≤ t i ∧ t i < 1) :
    0 ≤ S (sidePt 5 (t 5)) (sidePt 0 (t 0)) (innerVtx 5) := by
  obtain ⟨h50, h51⟩ := ht 5
  obtain ⟨h00, h01⟩ := ht 0
  have hEq : S (sidePt 5 (t 5)) (sidePt 0 (t 0)) (innerVtx 5) =
      scale ^ 2 * (Real.sqrt 3 / 2) * (((1 - t 5) * (1 - t 0) + 2 * t 5 * t 0) / 3) := by
    expandS
  have hs3 : (0:ℝ) < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have e1 : (0:ℝ) ≤ (1 - t 5) * (1 - t 0) :=
    mul_nonneg (sub_nonneg.2 h51.le) (sub_nonneg.2 h01.le)
  have e2 : (0:ℝ) ≤ 2 * t 5 * t 0 := mul_nonneg (mul_nonneg (by norm_num) h50) h00
  rw [hEq]
  exact mul_nonneg (mul_nonneg (pow_pos scale_pos 2).le (half_pos hs3).le) (by linarith)

lemma S_sidePt_mirror_nonneg_1 {t : Fin 6 → ℝ} (ht : ∀ i : Fin 6, 0 ≤ t i ∧ t i < 1) :
    0 ≤ S (sidePt 1 (t 1)) (innerVtx 1) (innerVtx 0) := by
  obtain ⟨h10, h11⟩ := ht 1
  have hEq : S (sidePt 1 (t 1)) (innerVtx 1) (innerVtx 0) =
      scale ^ 2 * (Real.sqrt 3 / 2) * ((1 - t 1) / 3) := by
    expandS
  have hs3 : (0:ℝ) < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  rw [hEq]
  exact mul_nonneg (mul_nonneg (pow_pos scale_pos 2).le (half_pos hs3).le) (by linarith)

lemma S_sidePt_mirror_nonneg_2 {t : Fin 6 → ℝ} (ht : ∀ i : Fin 6, 0 ≤ t i ∧ t i < 1) :
    0 ≤ S (sidePt 2 (t 2)) (innerVtx 2) (innerVtx 1) := by
  obtain ⟨h20, h21⟩ := ht 2
  have hEq : S (sidePt 2 (t 2)) (innerVtx 2) (innerVtx 1) =
      scale ^ 2 * (Real.sqrt 3 / 2) * ((1 - t 2) / 3) := by
    expandS
  have hs3 : (0:ℝ) < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  rw [hEq]
  exact mul_nonneg (mul_nonneg (pow_pos scale_pos 2).le (half_pos hs3).le) (by linarith)

lemma S_sidePt_mirror_nonneg_3 {t : Fin 6 → ℝ} (ht : ∀ i : Fin 6, 0 ≤ t i ∧ t i < 1) :
    0 ≤ S (sidePt 3 (t 3)) (innerVtx 3) (innerVtx 2) := by
  obtain ⟨h30, h31⟩ := ht 3
  have hEq : S (sidePt 3 (t 3)) (innerVtx 3) (innerVtx 2) =
      scale ^ 2 * (Real.sqrt 3 / 2) * ((1 - t 3) / 3) := by
    expandS
  have hs3 : (0:ℝ) < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  rw [hEq]
  exact mul_nonneg (mul_nonneg (pow_pos scale_pos 2).le (half_pos hs3).le) (by linarith)

lemma S_sidePt_mirror_nonneg_4 {t : Fin 6 → ℝ} (ht : ∀ i : Fin 6, 0 ≤ t i ∧ t i < 1) :
    0 ≤ S (sidePt 4 (t 4)) (innerVtx 4) (innerVtx 3) := by
  obtain ⟨h40, h41⟩ := ht 4
  have hEq : S (sidePt 4 (t 4)) (innerVtx 4) (innerVtx 3) =
      scale ^ 2 * (Real.sqrt 3 / 2) * ((1 - t 4) / 3) := by
    expandS
  have hs3 : (0:ℝ) < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  rw [hEq]
  exact mul_nonneg (mul_nonneg (pow_pos scale_pos 2).le (half_pos hs3).le) (by linarith)

lemma S_sidePt_mirror_nonneg_5 {t : Fin 6 → ℝ} (ht : ∀ i : Fin 6, 0 ≤ t i ∧ t i < 1) :
    0 ≤ S (sidePt 5 (t 5)) (innerVtx 5) (innerVtx 4) := by
  obtain ⟨h50, h51⟩ := ht 5
  have hEq : S (sidePt 5 (t 5)) (innerVtx 5) (innerVtx 4) =
      scale ^ 2 * (Real.sqrt 3 / 2) * ((1 - t 5) / 3) := by
    expandS
  have hs3 : (0:ℝ) < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  rw [hEq]
  exact mul_nonneg (mul_nonneg (pow_pos scale_pos 2).le (half_pos hs3).le) (by linarith)

/-- Order forcing: a bijection `σ` of `Fin 6` fixing `0` such that every
increasing triple of the permuted side points makes a left turn must be the
identity. Any other permutation has a backward triple whose side set is one of
the fourteen "good" triples, contradicting strict convexity. -/
lemma order_forcing {t : Fin 6 → ℝ} (ht : ∀ i : Fin 6, 0 ≤ t i ∧ t i < 1)
    {σ : Fin 6 → Fin 6} (hσ0 : σ 0 = 0) (hσb : Function.Bijective σ)
    (H : ∀ a b c : Fin 6, a < b → b < c →
      0 < S (sidePt (σ a) (t (σ a))) (sidePt (σ b) (t (σ b))) (sidePt (σ c) (t (σ c)))) :
    ∀ k : Fin 6, σ k = k := by
  have hsur : ∀ v : Fin 6, ∃ m : Fin 6, σ m = v := hσb.2
  have hσ1 : σ 1 = 1 := by
    obtain ⟨m1, hm1⟩ := hsur 1
    have hm1ne0 : m1 ≠ 0 := by
      intro hcon
      rw [hcon, hσ0] at hm1
      exact one_ne_zero hm1.symm
    by_cases hcase : m1 = 1
    · rw [hcase] at hm1
      exact hm1
    · exfalso
      have hm1gt : (1 : Fin 6) < m1 := by
        rw [Fin.lt_def]
        have e0 : m1.val ≠ 0 := fun hcon => hm1ne0 (Fin.ext hcon)
        have e1 : m1.val ≠ 1 := fun hcon => hcase (Fin.ext hcon)
        have := m1.isLt
        omega
      have hH := H 0 1 m1 (by decide) hm1gt
      rw [hσ0, hm1] at hH
      have hσ1ne0 : σ 1 ≠ 0 := by
        intro hcon
        have e := hσb.1 (show σ 1 = σ 0 from by rw [hcon, hσ0])
        exact one_ne_zero e
      have hσ1ne1 : σ 1 ≠ 1 := by
        intro hcon
        have e := hσb.1 (show σ 1 = σ m1 from by rw [hcon, hm1])
        exact hcase e.symm
      have hv : (σ 1).val = 2 ∨ (σ 1).val = 3 ∨ (σ 1).val = 4 ∨ (σ 1).val = 5 := by
        have e0 : (σ 1).val ≠ 0 := fun hcon => hσ1ne0 (Fin.ext hcon)
        have e1 : (σ 1).val ≠ 1 := fun hcon => hσ1ne1 (Fin.ext hcon)
        have := (σ 1).isLt
        omega
      rcases hv with h2 | h3 | h4 | h5
      · have e : σ 1 = 2 := Fin.ext h2
        rw [e] at hH
        have hbad := S_sidePt_pos_012 ht
        rw [S_swap_right] at hH
        linarith
      · have e : σ 1 = 3 := Fin.ext h3
        rw [e] at hH
        have hbad := S_sidePt_pos_013 ht
        rw [S_swap_right] at hH
        linarith
      · have e : σ 1 = 4 := Fin.ext h4
        rw [e] at hH
        have hbad := S_sidePt_pos_014 ht
        rw [S_swap_right] at hH
        linarith
      · have e : σ 1 = 5 := Fin.ext h5
        rw [e] at hH
        have hbad := S_sidePt_pos_015 ht
        rw [S_swap_right] at hH
        linarith
  have hσ2 : σ 2 = 2 := by
    obtain ⟨m2, hm2⟩ := hsur 2
    have hm2ne0 : m2 ≠ 0 := by
      intro hcon
      rw [hcon, hσ0] at hm2
      exact (by decide : (2 : Fin 6) ≠ 0) hm2.symm
    have hm2ne1 : m2 ≠ 1 := by
      intro hcon
      rw [hcon, hσ1] at hm2
      exact (by decide : (2 : Fin 6) ≠ 1) hm2.symm
    by_cases hcase : m2 = 2
    · rw [hcase] at hm2
      exact hm2
    · exfalso
      have hm2gt : (2 : Fin 6) < m2 := by
        rw [Fin.lt_def]
        have e0 : m2.val ≠ 0 := fun hcon => hm2ne0 (Fin.ext hcon)
        have e1 : m2.val ≠ 1 := fun hcon => hm2ne1 (Fin.ext hcon)
        have e2 : m2.val ≠ 2 := fun hcon => hcase (Fin.ext hcon)
        have := m2.isLt
        omega
      have hH02 := H 0 2 m2 (by decide) hm2gt
      have hH12 := H 1 2 m2 (by decide) hm2gt
      rw [hσ0, hm2] at hH02
      rw [hσ1, hm2] at hH12
      have hσ2ne0 : σ 2 ≠ 0 := by
        intro hcon
        have e := hσb.1 (show σ 2 = σ 0 from by rw [hcon, hσ0])
        exact (by decide : (2 : Fin 6) ≠ 0) e
      have hσ2ne1 : σ 2 ≠ 1 := by
        intro hcon
        have e := hσb.1 (show σ 2 = σ 1 from by rw [hcon, hσ1])
        exact (by decide : (2 : Fin 6) ≠ 1) e
      have hσ2ne2 : σ 2 ≠ 2 := by
        intro hcon
        have e := hσb.1 (show σ 2 = σ m2 from by rw [hcon, hm2])
        exact hcase e.symm
      have hv : (σ 2).val = 3 ∨ (σ 2).val = 4 ∨ (σ 2).val = 5 := by
        have e0 : (σ 2).val ≠ 0 := fun hcon => hσ2ne0 (Fin.ext hcon)
        have e1 : (σ 2).val ≠ 1 := fun hcon => hσ2ne1 (Fin.ext hcon)
        have e2 : (σ 2).val ≠ 2 := fun hcon => hσ2ne2 (Fin.ext hcon)
        have := (σ 2).isLt
        omega
      rcases hv with h3 | h4 | h5
      · have e : σ 2 = 3 := Fin.ext h3
        rw [e] at hH12
        have hbad := S_sidePt_pos_123 ht
        rw [S_swap_right] at hH12
        linarith
      · have e : σ 2 = 4 := Fin.ext h4
        rw [e] at hH12
        have hbad := S_sidePt_pos_124 ht
        rw [S_swap_right] at hH12
        linarith
      · have e : σ 2 = 5 := Fin.ext h5
        rw [e] at hH02
        have hbad := S_sidePt_pos_025 ht
        rw [S_swap_right] at hH02
        linarith
  have hσ3 : σ 3 = 3 := by
    obtain ⟨m3, hm3⟩ := hsur 3
    have hm3ne0 : m3 ≠ 0 := by
      intro hcon
      rw [hcon, hσ0] at hm3
      exact (by decide : (3 : Fin 6) ≠ 0) hm3.symm
    have hm3ne1 : m3 ≠ 1 := by
      intro hcon
      rw [hcon, hσ1] at hm3
      exact (by decide : (3 : Fin 6) ≠ 1) hm3.symm
    have hm3ne2 : m3 ≠ 2 := by
      intro hcon
      rw [hcon, hσ2] at hm3
      exact (by decide : (3 : Fin 6) ≠ 2) hm3.symm
    by_cases hcase : m3 = 3
    · rw [hcase] at hm3
      exact hm3
    · exfalso
      have hm3gt : (3 : Fin 6) < m3 := by
        rw [Fin.lt_def]
        have e0 : m3.val ≠ 0 := fun hcon => hm3ne0 (Fin.ext hcon)
        have e1 : m3.val ≠ 1 := fun hcon => hm3ne1 (Fin.ext hcon)
        have e2 : m3.val ≠ 2 := fun hcon => hm3ne2 (Fin.ext hcon)
        have e3 : m3.val ≠ 3 := fun hcon => hcase (Fin.ext hcon)
        have := m3.isLt
        omega
      have hH03 := H 0 3 m3 (by decide) hm3gt
      have hH23 := H 2 3 m3 (by decide) hm3gt
      rw [hσ0, hm3] at hH03
      rw [hσ2, hm3] at hH23
      have hσ3ne0 : σ 3 ≠ 0 := by
        intro hcon
        have e := hσb.1 (show σ 3 = σ 0 from by rw [hcon, hσ0])
        exact (by decide : (3 : Fin 6) ≠ 0) e
      have hσ3ne1 : σ 3 ≠ 1 := by
        intro hcon
        have e := hσb.1 (show σ 3 = σ 1 from by rw [hcon, hσ1])
        exact (by decide : (3 : Fin 6) ≠ 1) e
      have hσ3ne2 : σ 3 ≠ 2 := by
        intro hcon
        have e := hσb.1 (show σ 3 = σ 2 from by rw [hcon, hσ2])
        exact (by decide : (3 : Fin 6) ≠ 2) e
      have hσ3ne3 : σ 3 ≠ 3 := by
        intro hcon
        have e := hσb.1 (show σ 3 = σ m3 from by rw [hcon, hm3])
        exact hcase e.symm
      have hv : (σ 3).val = 4 ∨ (σ 3).val = 5 := by
        have e0 : (σ 3).val ≠ 0 := fun hcon => hσ3ne0 (Fin.ext hcon)
        have e1 : (σ 3).val ≠ 1 := fun hcon => hσ3ne1 (Fin.ext hcon)
        have e2 : (σ 3).val ≠ 2 := fun hcon => hσ3ne2 (Fin.ext hcon)
        have e3 : (σ 3).val ≠ 3 := fun hcon => hσ3ne3 (Fin.ext hcon)
        have := (σ 3).isLt
        omega
      rcases hv with h4 | h5
      · have e : σ 3 = 4 := Fin.ext h4
        rw [e] at hH03
        have hbad := S_sidePt_pos_034 ht
        rw [S_swap_right] at hH03
        linarith
      · have e : σ 3 = 5 := Fin.ext h5
        rw [e] at hH23
        have hbad := S_sidePt_pos_235 ht
        rw [S_swap_right] at hH23
        linarith
  have hσ4 : σ 4 = 4 := by
    obtain ⟨m4, hm4⟩ := hsur 4
    have hm4ne0 : m4 ≠ 0 := by
      intro hcon
      rw [hcon, hσ0] at hm4
      exact (by decide : (4 : Fin 6) ≠ 0) hm4.symm
    have hm4ne1 : m4 ≠ 1 := by
      intro hcon
      rw [hcon, hσ1] at hm4
      exact (by decide : (4 : Fin 6) ≠ 1) hm4.symm
    have hm4ne2 : m4 ≠ 2 := by
      intro hcon
      rw [hcon, hσ2] at hm4
      exact (by decide : (4 : Fin 6) ≠ 2) hm4.symm
    have hm4ne3 : m4 ≠ 3 := by
      intro hcon
      rw [hcon, hσ3] at hm4
      exact (by decide : (4 : Fin 6) ≠ 3) hm4.symm
    by_cases hcase : m4 = 4
    · rw [hcase] at hm4
      exact hm4
    · exfalso
      have hm4eq : m4 = 5 := by
        have e0 : m4.val ≠ 0 := fun hcon => hm4ne0 (Fin.ext hcon)
        have e1 : m4.val ≠ 1 := fun hcon => hm4ne1 (Fin.ext hcon)
        have e2 : m4.val ≠ 2 := fun hcon => hm4ne2 (Fin.ext hcon)
        have e3 : m4.val ≠ 3 := fun hcon => hm4ne3 (Fin.ext hcon)
        have e4 : m4.val ≠ 4 := fun hcon => hcase (Fin.ext hcon)
        have := m4.isLt
        exact Fin.ext (by omega)
      have hH := H 0 4 5 (by decide) (by decide)
      rw [hm4eq] at hm4
      rw [hσ0, hm4] at hH
      have hσ4ne : σ 4 = 5 := by
        have hσ4ne0 : σ 4 ≠ 0 := by
          intro hcon
          have e := hσb.1 (show σ 4 = σ 0 from by rw [hcon, hσ0])
          exact (by decide : (4 : Fin 6) ≠ 0) e
        have hσ4ne1 : σ 4 ≠ 1 := by
          intro hcon
          have e := hσb.1 (show σ 4 = σ 1 from by rw [hcon, hσ1])
          exact (by decide : (4 : Fin 6) ≠ 1) e
        have hσ4ne2 : σ 4 ≠ 2 := by
          intro hcon
          have e := hσb.1 (show σ 4 = σ 2 from by rw [hcon, hσ2])
          exact (by decide : (4 : Fin 6) ≠ 2) e
        have hσ4ne3 : σ 4 ≠ 3 := by
          intro hcon
          have e := hσb.1 (show σ 4 = σ 3 from by rw [hcon, hσ3])
          exact (by decide : (4 : Fin 6) ≠ 3) e
        have hσ4ne4 : σ 4 ≠ 4 := by
          intro hcon
          have e := hσb.1 (show σ 4 = σ m4 from by rw [hcon, hm4eq, hm4])
          exact hcase e.symm
        have e0 : (σ 4).val ≠ 0 := fun hcon => hσ4ne0 (Fin.ext hcon)
        have e1 : (σ 4).val ≠ 1 := fun hcon => hσ4ne1 (Fin.ext hcon)
        have e2 : (σ 4).val ≠ 2 := fun hcon => hσ4ne2 (Fin.ext hcon)
        have e3 : (σ 4).val ≠ 3 := fun hcon => hσ4ne3 (Fin.ext hcon)
        have e4 : (σ 4).val ≠ 4 := fun hcon => hσ4ne4 (Fin.ext hcon)
        have := (σ 4).isLt
        exact Fin.ext (by omega)
      rw [hσ4ne] at hH
      have hbad := S_sidePt_pos_045 ht
      rw [S_swap_right] at hH
      linarith
  have hσ5 : σ 5 = 5 := by
    have hσ5ne0 : σ 5 ≠ 0 := by
      intro hcon
      have e := hσb.1 (show σ 5 = σ 0 from by rw [hcon, hσ0])
      exact (by decide : (5 : Fin 6) ≠ 0) e
    have hσ5ne1 : σ 5 ≠ 1 := by
      intro hcon
      have e := hσb.1 (show σ 5 = σ 1 from by rw [hcon, hσ1])
      exact (by decide : (5 : Fin 6) ≠ 1) e
    have hσ5ne2 : σ 5 ≠ 2 := by
      intro hcon
      have e := hσb.1 (show σ 5 = σ 2 from by rw [hcon, hσ2])
      exact (by decide : (5 : Fin 6) ≠ 2) e
    have hσ5ne3 : σ 5 ≠ 3 := by
      intro hcon
      have e := hσb.1 (show σ 5 = σ 3 from by rw [hcon, hσ3])
      exact (by decide : (5 : Fin 6) ≠ 3) e
    have hσ5ne4 : σ 5 ≠ 4 := by
      intro hcon
      have e := hσb.1 (show σ 5 = σ 4 from by rw [hcon, hσ4])
      exact (by decide : (5 : Fin 6) ≠ 4) e
    have e0 : (σ 5).val ≠ 0 := fun hcon => hσ5ne0 (Fin.ext hcon)
    have e1 : (σ 5).val ≠ 1 := fun hcon => hσ5ne1 (Fin.ext hcon)
    have e2 : (σ 5).val ≠ 2 := fun hcon => hσ5ne2 (Fin.ext hcon)
    have e3 : (σ 5).val ≠ 3 := fun hcon => hσ5ne3 (Fin.ext hcon)
    have e4 : (σ 5).val ≠ 4 := fun hcon => hσ5ne4 (Fin.ext hcon)
    have := (σ 5).isLt
    exact Fin.ext (by omega)
  intro k
  fin_cases k
  · exact hσ0
  · exact hσ1
  · exact hσ2
  · exact hσ3
  · exact hσ4
  · exact hσ5

/-- Extracting a 6-gon from cyclically increasing vertices shrinks the shoelace
sum: rotate so the first index is `0`, apply `extraction_bound`, rotate back. -/
lemma shoelace_extract {l : List Pt} (h : ConvexPos l)
    (d : Fin 6 → ℕ) (hd_mono : ∀ a b : Fin 6, a < b → d a < d b)
    (hd_lt : ∀ k : Fin 6, d k < l.length) :
    shoelace [(l[d 0]'(hd_lt 0)), (l[d 1]'(hd_lt 1)), (l[d 2]'(hd_lt 2)), (l[d 3]'(hd_lt 3)),
      (l[d 4]'(hd_lt 4)), (l[d 5]'(hd_lt 5))] ≤ shoelace l := by
  have hd0_le : ∀ k : Fin 6, d 0 ≤ d k := by
    intro k
    rcases (by omega : k = 0 ∨ 0 < k) with rfl | hk
    · exact le_refl _
    · exact (hd_mono 0 k hk).le
  have hrot : shoelace (l.rotate (d 0)) = shoelace l := shoelace_rotate l (d 0)
  have hconv : ConvexPos (l.rotate (d 0)) := h.rotate_of_le (by have := hd_lt 0; omega)
  have hlt : ∀ k : Fin 6, d k - d 0 < (l.rotate (d 0)).length := by
    intro k
    rw [List.length_rotate]
    have := hd_lt k
    omega
  have he := extraction_bound hconv (fun k => d k - d 0) (by omega)
    (fun a b hab => by have h1 := hd_mono a b hab; have h2 := hd0_le a; omega) hlt
  have hdk : ∀ k : Fin 6, (l.rotate (d 0))[d k - d 0]'(hlt k) = l[d k]'(hd_lt k) := by
    intro k
    rw [List.getElem_rotate]
    exact getElem_congr_idx _ _ (by rw [Nat.sub_add_cancel (hd0_le k), Nat.mod_eq_of_lt (hd_lt k)])
  rw [hdk 0, hdk 1, hdk 2, hdk 3, hdk 4, hdk 5, hrot] at he
  exact he

/-- The extracted 6-gon of cyclically increasing vertices is in convex position. -/
lemma ConvexPos_extract {l : List Pt} (h : ConvexPos l)
    (d : Fin 6 → ℕ) (hd_mono : ∀ a b : Fin 6, a < b → d a < d b)
    (hd_lt : ∀ k : Fin 6, d k < l.length) :
    ConvexPos [(l[d 0]'(hd_lt 0)), (l[d 1]'(hd_lt 1)), (l[d 2]'(hd_lt 2)), (l[d 3]'(hd_lt 3)),
      (l[d 4]'(hd_lt 4)), (l[d 5]'(hd_lt 5))] := by
  rw [ConvexPos.of_triplewise]
  intro i j k hij hjk hk
  have hget : ∀ m : ℕ, ∀ hm : m < 6, ([l[d 0]'(hd_lt 0), l[d 1]'(hd_lt 1), l[d 2]'(hd_lt 2),
      l[d 3]'(hd_lt 3), l[d 4]'(hd_lt 4), l[d 5]'(hd_lt 5)] : List Pt)[m]'(by simp; omega) =
      l[d ⟨m, hm⟩]'(hd_lt ⟨m, hm⟩) := by
    intro m hm
    interval_cases m <;> rfl
  have hk6 : k < 6 := by simpa using hk
  rw [hget i (by omega), hget j (by omega), hget k (by omega)]
  exact h.cyc (hd_lt ⟨i, by omega⟩) (hd_lt ⟨j, by omega⟩) (hd_lt ⟨k, by omega⟩)
    (Or.inl ⟨hd_mono ⟨i, by omega⟩ ⟨j, by omega⟩ (by simp only [Fin.mk_lt_mk]; omega),
      hd_mono ⟨j, by omega⟩ ⟨k, by omega⟩ (by simp only [Fin.mk_lt_mk]; omega)⟩)

/-- Sorting an injective `Fin 6 → ℕ` yields a strictly monotone enumeration
precomposed with a bijection. -/
lemma sort_bijection {j : Fin 6 → ℕ} (hinj : Function.Injective j) :
    ∃ (d : Fin 6 → ℕ) (ρ : Fin 6 → Fin 6),
      (∀ a b : Fin 6, a < b → d a < d b) ∧ (∀ k, j (ρ k) = d k) ∧
      Function.Bijective ρ := by
  have hcard : (Finset.univ.image j).card = 6 := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  set s := Finset.univ.image j with hs
  have hmem : ∀ k : Fin 6, s.orderEmbOfFin hcard k ∈ s :=
    Finset.orderEmbOfFin_mem s hcard
  have hsurj : ∀ k : Fin 6, ∃ c : Fin 6, j c = s.orderEmbOfFin hcard k := by
    intro k
    obtain ⟨c, -, hc⟩ := Finset.mem_image.1 (by rw [← hs]; exact hmem k)
    exact ⟨c, hc⟩
  choose ρ hρ using hsurj
  have hinjρ : Function.Injective ρ := by
    intro a b hab
    have h1 : (s.orderEmbOfFin hcard) a = (s.orderEmbOfFin hcard) b := by
      rw [← hρ a, ← hρ b, hab]
    exact (s.orderEmbOfFin hcard).strictMono.injective h1
  exact ⟨s.orderEmbOfFin hcard, ρ,
    fun a b hab => (s.orderEmbOfFin hcard).strictMono.lt_iff_lt.2 hab, hρ,
    Finite.injective_iff_bijective.1 hinjρ⟩

/-- The shoelace sum of a six-element `List.ofFn` as an explicit sum of
cross products. -/
lemma shoelace_ofFn6 (f : Fin 6 → Pt) :
    shoelace (List.ofFn f) = cr (f 0) (f 1) + cr (f 1) (f 2) + cr (f 2) (f 3) +
      cr (f 3) (f 4) + cr (f 4) (f 5) + cr (f 5) (f 0) := by
  simp [shoelace]
  ring

/-- The dent identity: the shoelace sum of the 6-gon through one point on each
side of the hexagon equals the shoelace sum of the inner hexagon plus the
twelve (nonnegative) triangle terms at the dents. -/
lemma dent_identity (q : Fin 6 → Pt) :
    shoelace (List.ofFn q) = shoelace innerList +
      (S (q 0) (q 1) (innerVtx 0) + S (q 1) (innerVtx 1) (innerVtx 0) +
       S (q 1) (q 2) (innerVtx 1) + S (q 2) (innerVtx 2) (innerVtx 1) +
       S (q 2) (q 3) (innerVtx 2) + S (q 3) (innerVtx 3) (innerVtx 2) +
       S (q 3) (q 4) (innerVtx 3) + S (q 4) (innerVtx 4) (innerVtx 3) +
       S (q 4) (q 5) (innerVtx 4) + S (q 5) (innerVtx 5) (innerVtx 4) +
       S (q 5) (q 0) (innerVtx 5) + S (q 0) (innerVtx 0) (innerVtx 5)) := by
  rw [shoelace_ofFn6 q, show innerList = List.ofFn innerVtx from rfl,
    shoelace_ofFn6 innerVtx]
  simp only [S_eq_cr_add]
  rw [cr_comm (innerVtx 0) (q 1), cr_comm (innerVtx 1) (q 2), cr_comm (innerVtx 2) (q 3),
    cr_comm (innerVtx 3) (q 4), cr_comm (innerVtx 4) (q 5), cr_comm (innerVtx 5) (q 0),
    cr_comm (innerVtx 0) (q 0), cr_comm (innerVtx 1) (q 1), cr_comm (innerVtx 2) (q 2),
    cr_comm (innerVtx 3) (q 3), cr_comm (innerVtx 4) (q 4), cr_comm (innerVtx 5) (q 5),
    cr_comm (innerVtx 1) (innerVtx 0), cr_comm (innerVtx 2) (innerVtx 1),
    cr_comm (innerVtx 3) (innerVtx 2), cr_comm (innerVtx 4) (innerVtx 3),
    cr_comm (innerVtx 5) (innerVtx 4), cr_comm (innerVtx 0) (innerVtx 5)]
  ring

/-- Twice the area of the inner hexagon is `2/3`, so its area is `1/3`. -/
lemma shoelace_innerList : shoelace innerList = 2 / 3 := by
  have h : shoelace innerList = scale ^ 2 * Real.sqrt 3 := by
    simp [shoelace, innerList, cr, innerVtx, innerV, smul_eq_mul]
    ring_nf
  rw [h, scale_sq]
  field_simp

snip end

/-- USAMO 1997, Problem 4: every polygon obtained from the regular hexagon of
area `1` by repeated corner clipping has area greater than `1/3`. -/
problem usa1997_p4 {l : List Pt} (h : Reachable l) :
    (1/3 : ℝ) < (1/2) * shoelace l := by
  obtain ⟨h6, hcp, -, hside⟩ := bundle_of_reachable h
  obtain ⟨j, t, hj, ht, heq, hinj⟩ := selection_exists h6 hcp hside
  obtain ⟨d, ρ, hd_mono, hρ, hρb⟩ := sort_bijection hinj
  have hd_lt : ∀ k : Fin 6, d k < l.length := fun k => hρ k ▸ hj (ρ k)
  set P : List Pt := [(l[d 0]'(hd_lt 0)), (l[d 1]'(hd_lt 1)), (l[d 2]'(hd_lt 2)),
    (l[d 3]'(hd_lt 3)), (l[d 4]'(hd_lt 4)), (l[d 5]'(hd_lt 5))] with hPdef
  have hPlen : P.length = 6 := by simp [hPdef]
  have hPconv : ConvexPos P := by
    rw [hPdef]
    exact ConvexPos_extract hcp d hd_mono hd_lt
  have hPbound : shoelace P ≤ shoelace l := by
    rw [hPdef]
    exact shoelace_extract hcp d hd_mono hd_lt
  obtain ⟨i₀, hi₀⟩ := hρb.2 0
  set P' := P.rotate i₀.val with hP'def
  set σ : Fin 6 → Fin 6 := fun m => ρ (i₀ + m) with hσdef
  have hP'len : P'.length = 6 := by rw [hP'def, List.length_rotate, hPlen]
  have hP'conv : ConvexPos P' := hPconv.rotate_of_le (by rw [hPlen]; exact i₀.isLt.le)
  have hP'bound : shoelace P' ≤ shoelace l := by
    rw [hP'def, shoelace_rotate]
    exact hPbound
  have hσ0 : σ 0 = 0 := by
    rw [hσdef]
    show ρ (i₀ + 0) = 0
    rw [Fin.add_zero]
    exact hi₀
  have hσb : Function.Bijective σ := by
    rw [hσdef]
    exact hρb.comp (Equiv.addLeft i₀).bijective
  have hPget : ∀ m : ℕ, ∀ hm : m < 6, P[m]'(by rw [hPlen]; omega) =
      l[d ⟨m, hm⟩]'(hd_lt ⟨m, hm⟩) := by
    intro m hm
    apply getElem_of_getElem?
    rw [hPdef]
    interval_cases m <;> rfl
  have hP'get : ∀ m : Fin 6, P'[m.val]'(by rw [hP'len]; exact m.isLt) =
      sidePt (σ m) (t (σ m)) := by
    intro m
    apply getElem_of_getElem?
    rw [hP'def, List.getElem?_rotate (by rw [hPlen]; exact m.isLt), hPlen,
      List.getElem?_eq_getElem (h := by rw [hPlen]; omega)]
    have e2 := hPget ((m.val + i₀.val) % 6) (Nat.mod_lt _ (by omega))
    have e3 : l[d ⟨(m.val + i₀.val) % 6, Nat.mod_lt _ (by omega)⟩]'(hd_lt _) =
        l[j (ρ ⟨(m.val + i₀.val) % 6, Nat.mod_lt _ (by omega)⟩)]'(hj _) :=
      getElem_congr_idx _ _ (hρ _).symm
    have e4 := heq (ρ ⟨(m.val + i₀.val) % 6, Nat.mod_lt _ (by omega)⟩)
    have e5 : ρ ⟨(m.val + i₀.val) % 6, Nat.mod_lt _ (by omega)⟩ = σ m := by
      rw [hσdef]
      show ρ ⟨(m.val + i₀.val) % 6, Nat.mod_lt _ (by omega)⟩ = ρ (i₀ + m)
      congr 1
      exact Fin.ext (by rw [Fin.val_add, Nat.add_comm])
    rw [e2, e3, e4, e5]
  have H : ∀ a b c : Fin 6, a < b → b < c →
      0 < S (sidePt (σ a) (t (σ a))) (sidePt (σ b) (t (σ b))) (sidePt (σ c) (t (σ c))) := by
    intro a b c hab hbc
    rw [ConvexPos.of_triplewise] at hP'conv
    have h2 := hP'conv a.val b.val c.val hab hbc (by rw [hP'len]; exact c.isLt)
    rw [hP'get a, hP'get b, hP'get c] at h2
    exact h2
  have hσid : ∀ k : Fin 6, σ k = k := order_forcing ht hσ0 hσb H
  have hP'eq : P' = List.ofFn (fun c => sidePt c (t c)) := by
    apply List.ext_getElem (by rw [hP'len, List.length_ofFn])
    intro m hm1 hm2
    rw [List.getElem_ofFn]
    have hm6 : m < 6 := by rw [hP'len] at hm1; exact hm1
    have e := hP'get ⟨m, hm6⟩
    rw [hσid] at e
    exact e
  rw [hP'eq] at hP'bound
  have hdent := dent_identity (fun c => sidePt c (t c))
  beta_reduce at hdent
  have hinner : shoelace innerList = 2 / 3 := shoelace_innerList
  have g0 := S_sidePt_dent_nonneg_0 ht
  have g1 := S_sidePt_dent_nonneg_1 ht
  have g2 := S_sidePt_dent_nonneg_2 ht
  have g3 := S_sidePt_dent_nonneg_3 ht
  have g4 := S_sidePt_dent_nonneg_4 ht
  have g5 := S_sidePt_dent_nonneg_5 ht
  have m1 := S_sidePt_mirror_nonneg_1 ht
  have m2 := S_sidePt_mirror_nonneg_2 ht
  have m3 := S_sidePt_mirror_nonneg_3 ht
  have m4 := S_sidePt_mirror_nonneg_4 ht
  have m5 := S_sidePt_mirror_nonneg_5 ht
  have gap := S_sidePt_strict_gap ht
  linarith

end Usa1997P4
