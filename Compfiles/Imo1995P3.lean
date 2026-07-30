/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Tactic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Olympiad 1995, Problem 3

Determine all integers n > 3 for which there exist n points A₁, A₂, ..., Aₙ
in the plane, no three collinear, and real numbers r₁, r₂, ..., rₙ such that
for any distinct i, j, k, the area of the triangle AᵢAⱼAₖ is rᵢ + rⱼ + rₖ.
-/

namespace Imo1995P3

/-- The Euclidean plane. -/
abbrev Pt := EuclideanSpace ℝ (Fin 2)

/-- The answer: only `n = 4`. -/
determine solution_set : Set ℕ := { 4 }

snip begin

/-- The scalar 2D cross product. -/
def cross (x y : Pt) : ℝ := x 0 * y 1 - x 1 * y 0

/-- Twice the signed area of the triangle `ABC` (positive when `ABC` is
oriented counterclockwise).  Note that `darea A B C ≠ 0` is exactly the
condition that `A`, `B`, `C` are not collinear, and `|darea A B C| / 2` is
the ordinary unsigned area of the triangle. -/
def darea (A B C : Pt) : ℝ := cross (B - A) (C - A)

/-- The configuration whose existence is to be determined: `n` points in the
plane, no three collinear (expressed via the nonvanishing of the doubled
signed area), together with real numbers `r i` such that the area of every
triangle `A i A j A k` equals `r i + r j + r k`. -/
def Config (n : ℕ) : Prop :=
  ∃ A : Fin n → Pt, ∃ r : Fin n → ℝ,
    (∀ i j k : Fin n, i ≠ j → j ≠ k → i ≠ k → darea (A i) (A j) (A k) ≠ 0) ∧
    ∀ i j k : Fin n, i ≠ j → j ≠ k → i ≠ k →
      |darea (A i) (A j) (A k)| / 2 = r i + r j + r k

lemma Pt_ext {x y : Pt} (h : ∀ i, x i = y i) : x = y := by
  apply WithLp.ofLp_injective (p := 2)
  funext i
  exact h i

/-! ### Basic algebraic identities for `cross` and `darea` -/

lemma darea_rot (A B C : Pt) : darea A B C = darea B C A := by
  simp [darea, cross, PiLp.sub_apply]; ring

lemma darea_swap21 (A B C : Pt) : darea B A C = -darea A B C := by
  simp [darea, cross, PiLp.sub_apply]; ring

lemma darea_swap32 (A B C : Pt) : darea A C B = -darea A B C := by
  simp [darea, cross, PiLp.sub_apply]; ring

/-- The cocycle identity for four points. -/
lemma darea_cocycle (A B C D : Pt) :
    darea B C D - darea A C D + darea A B D - darea A B C = 0 := by
  simp [darea, cross, PiLp.sub_apply]; ring

/-- The area addition identity: `ABC = XBC + AXC + ABX`. -/
lemma darea_id (A B C X : Pt) :
    darea A B C = darea X B C + darea A X C + darea A B X := by
  simp [darea, cross, PiLp.sub_apply]; ring

/-- Two vectors both "parallel" (in the cross-product sense) to a common
nonzero vector are parallel to each other. -/
lemma cross_parallel_trans {u v w : Pt} (huw : cross u w = 0) (hvw : cross v w = 0)
    (hw : w ≠ 0) : cross u v = 0 := by
  have hne : w 0 ≠ 0 ∨ w 1 ≠ 0 := by
    by_contra h
    push Not at h
    exact hw (Pt_ext (fun i => by fin_cases i <;> simp [h.1, h.2]))
  rcases hne with hw0 | hw1
  · have key : cross u v * w 0 = v 0 * cross u w - u 0 * cross v w := by
      simp [cross]; ring
    rw [huw, hvw, mul_zero, mul_zero, sub_zero] at key
    rcases mul_eq_zero.mp key with h | h
    · exact h
    · exact absurd h hw0
  · have key : cross u v * w 1 = v 1 * cross u w - u 1 * cross v w := by
      simp [cross]; ring
    rw [huw, hvw, mul_zero, mul_zero, sub_zero] at key
    rcases mul_eq_zero.mp key with h | h
    · exact h
    · exact absurd h hw1

lemma cross_neg_left (x y v : Pt) : cross (x - y) v = -cross (y - x) v := by
  simp [cross, PiLp.sub_apply]; ring

/-- The midpoint condition transported to the other endpoint of a segment. -/
lemma mid_flip (x y d e : Pt) :
    cross (x - y) (e + d - (2 : ℝ) • y) = -cross (y - x) (e + d - (2 : ℝ) • x) := by
  simp [cross, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply]; ring

/-! ### Sign bookkeeping -/

/-- If `ε` is a sign and `ε * x` is positive, then `ε * y` is positive whenever
`x * y` is. -/
lemma eps_mul_pos {x y : ℝ} (h : 0 < x * y) {ε : ℝ} (hε : ε * ε = 1) (hx : 0 < ε * x) :
    0 < ε * y := by
  have h1 : 0 < (ε * x) * (ε * y) := by
    have he : (ε * x) * (ε * y) = (ε * ε) * (x * y) := by ring
    rw [he, hε, one_mul]
    exact h
  exact pos_of_mul_pos_right h1 hx.le

/-- If `ε` is a sign with `ε * x > 0`, then `|x| = ε * x`. -/
lemma abs_eq_eps_mul {x : ℝ} {ε : ℝ} (hε : ε * ε = 1) (hx : 0 < ε * x) :
    |x| = ε * x := by
  have h1 : |ε * x| = ε * x := abs_of_pos hx
  have h2 : |ε * x| = |ε| * |x| := abs_mul ε x
  have h3 : |ε| = 1 := by
    have h4 : ε ^ 2 = 1 := by linear_combination hε
    rcases sq_eq_one_iff.mp h4 with h | h <;> simp [h]
  rw [h2, h3, one_mul] at h1
  exact h1

/-- The sign of the (nonzero) `darea (A a) (A b) (A c)`. -/
noncomputable def esign (A : Fin 5 → Pt) (a b c : Fin 5) : ℝ :=
  if 0 < darea (A a) (A b) (A c) then 1 else -1

lemma esign_sq {A : Fin 5 → Pt} {a b c : Fin 5} : esign A a b c * esign A a b c = 1 := by
  by_cases h : 0 < darea (A a) (A b) (A c) <;> simp [esign, h]

lemma esign_pos {A : Fin 5 → Pt} {a b c : Fin 5}
    (h : darea (A a) (A b) (A c) ≠ 0) : 0 < esign A a b c * darea (A a) (A b) (A c) := by
  by_cases hσ : 0 < darea (A a) (A b) (A c)
  · simp [esign, hσ]
  · have h2 : darea (A a) (A b) (A c) < 0 := lt_of_le_of_ne (le_of_not_gt hσ) h
    simp [esign, hσ]
    linarith

/-! ### `ConvQuad` and `Inside`: sign descriptions of configurations

`ConvQuad A a b c d` says that the four points are in convex position, in this
cyclic order (either all counterclockwise or all clockwise); equivalently the
four triangles have consistently oriented signed areas.

`Inside A x a b c` says that `x` lies strictly inside the triangle `a b c`;
equivalently `x` is on the same side of each edge as the opposite vertex. -/

def ConvQuad (A : Fin 5 → Pt) (a b c d : Fin 5) : Prop :=
  0 < darea (A a) (A b) (A c) * darea (A b) (A c) (A d) ∧
  0 < darea (A b) (A c) (A d) * darea (A c) (A d) (A a) ∧
  0 < darea (A c) (A d) (A a) * darea (A d) (A a) (A b)

def Inside (A : Fin 5 → Pt) (x a b c : Fin 5) : Prop :=
  0 < darea (A a) (A b) (A c) * darea (A x) (A b) (A c) ∧
  0 < darea (A a) (A b) (A c) * darea (A a) (A x) (A c) ∧
  0 < darea (A a) (A b) (A c) * darea (A a) (A b) (A x)

/-- A convex quadrilateral split along a diagonal in two ways:
`q a + q c = q b + q d`. -/
lemma ConvQuad_rel {A : Fin 5 → Pt} {q : Fin 5 → ℝ} {a b c d : Fin 5}
    (hcoll : ∀ i j k : Fin 5, i ≠ j → j ≠ k → i ≠ k → darea (A i) (A j) (A k) ≠ 0)
    (harea : ∀ i j k : Fin 5, i ≠ j → j ≠ k → i ≠ k →
      |darea (A i) (A j) (A k)| = q i + q j + q k)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (h : ConvQuad A a b c d) : q a + q c = q b + q d := by
  obtain ⟨h1, h2, h3⟩ := h
  have nabc := hcoll a b c hab hbc hac
  have hεε : esign A a b c * esign A a b c = 1 := esign_sq
  have hε0 : 0 < esign A a b c * darea (A a) (A b) (A c) := esign_pos nabc
  have hε1 := eps_mul_pos h1 hεε hε0
  have hε2 := eps_mul_pos h2 hεε hε1
  have hε3 := eps_mul_pos h3 hεε hε2
  have a1 := abs_eq_eps_mul hεε hε0
  have a2 := abs_eq_eps_mul hεε hε1
  have a3 := abs_eq_eps_mul hεε hε2
  have a4 := abs_eq_eps_mul hεε hε3
  have hrot1 : darea (A a) (A c) (A d) = darea (A c) (A d) (A a) := darea_rot _ _ _
  have hrot2 : darea (A a) (A b) (A d) = darea (A d) (A a) (A b) :=
    (darea_rot _ _ _).trans (darea_rot _ _ _)
  have hcyc : esign A a b c * darea (A b) (A c) (A d) -
      esign A a b c * darea (A c) (A d) (A a) +
      esign A a b c * darea (A d) (A a) (A b) -
      esign A a b c * darea (A a) (A b) (A c) = 0 := by
    have h := darea_cocycle (A a) (A b) (A c) (A d)
    linear_combination esign A a b c * h + esign A a b c * hrot1 -
      esign A a b c * hrot2
  have eabc := harea a b c hab hbc hac
  have ebcd := harea b c d hbc hcd hbd
  have eacd := harea a c d hac hcd had
  have eabd := harea a b d hab hbd had
  rw [a1] at eabc
  rw [a2] at ebcd
  rw [hrot1, a3] at eacd
  rw [hrot2, a4] at eabd
  linarith

/-- A point strictly inside a triangle splits it into three triangles:
`q a + q b + q c + 3 * q x = 0`. -/
lemma Inside_rel {A : Fin 5 → Pt} {q : Fin 5 → ℝ} {x a b c : Fin 5}
    (hcoll : ∀ i j k : Fin 5, i ≠ j → j ≠ k → i ≠ k → darea (A i) (A j) (A k) ≠ 0)
    (harea : ∀ i j k : Fin 5, i ≠ j → j ≠ k → i ≠ k →
      |darea (A i) (A j) (A k)| = q i + q j + q k)
    (hxa : x ≠ a) (hxb : x ≠ b) (hxc : x ≠ c) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (h : Inside A x a b c) : q a + q b + q c + 3 * q x = 0 := by
  obtain ⟨h1, h2, h3⟩ := h
  have nabc := hcoll a b c hab hbc hac
  have hεε : esign A a b c * esign A a b c = 1 := esign_sq
  have hε0 : 0 < esign A a b c * darea (A a) (A b) (A c) := esign_pos nabc
  have hε1 := eps_mul_pos h1 hεε hε0
  have hε2 := eps_mul_pos h2 hεε hε0
  have hε3 := eps_mul_pos h3 hεε hε0
  have a1 := abs_eq_eps_mul hεε hε0
  have a2 := abs_eq_eps_mul hεε hε1
  have a3 := abs_eq_eps_mul hεε hε2
  have a4 := abs_eq_eps_mul hεε hε3
  have hcyc : esign A a b c * darea (A a) (A b) (A c) =
      esign A a b c * darea (A x) (A b) (A c) +
      esign A a b c * darea (A a) (A x) (A c) +
      esign A a b c * darea (A a) (A b) (A x) := by
    have h := darea_id (A a) (A b) (A c) (A x)
    linear_combination esign A a b c * h
  have eabc := harea a b c hab hbc hac
  have exbc := harea x b c hxb hbc hxc
  have eaxc := harea a x c (Ne.symm hxa) hxc hac
  have eabx := harea a b x hab (Ne.symm hxb) (Ne.symm hxa)
  rw [a1] at eabc
  rw [a2] at exbc
  rw [a3] at eaxc
  rw [a4] at eabx
  linarith

/-! ### The five Plücker relations among the `darea` values of five points -/

lemma plucker0 (A : Fin 5 → Pt) :
    darea (A 0) (A 1) (A 2) * darea (A 0) (A 3) (A 4) -
    darea (A 0) (A 1) (A 3) * darea (A 0) (A 2) (A 4) +
    darea (A 0) (A 1) (A 4) * darea (A 0) (A 2) (A 3) = 0 := by
  simp [darea, cross, PiLp.sub_apply]; ring

lemma plucker1 (A : Fin 5 → Pt) :
    -(darea (A 0) (A 1) (A 2) * darea (A 1) (A 3) (A 4)) +
    darea (A 0) (A 1) (A 3) * darea (A 1) (A 2) (A 4) -
    darea (A 0) (A 1) (A 4) * darea (A 1) (A 2) (A 3) = 0 := by
  simp [darea, cross, PiLp.sub_apply]; ring

lemma plucker2 (A : Fin 5 → Pt) :
    darea (A 0) (A 1) (A 2) * darea (A 2) (A 3) (A 4) -
    darea (A 0) (A 2) (A 3) * darea (A 1) (A 2) (A 4) +
    darea (A 0) (A 2) (A 4) * darea (A 1) (A 2) (A 3) = 0 := by
  simp [darea, cross, PiLp.sub_apply]; ring

lemma plucker3 (A : Fin 5 → Pt) :
    -(darea (A 0) (A 1) (A 3) * darea (A 2) (A 3) (A 4)) +
    darea (A 0) (A 2) (A 3) * darea (A 1) (A 3) (A 4) -
    darea (A 0) (A 3) (A 4) * darea (A 1) (A 2) (A 3) = 0 := by
  simp [darea, cross, PiLp.sub_apply]; ring

lemma plucker4 (A : Fin 5 → Pt) :
    darea (A 0) (A 1) (A 4) * darea (A 2) (A 3) (A 4) -
    darea (A 0) (A 2) (A 4) * darea (A 1) (A 3) (A 4) +
    darea (A 0) (A 3) (A 4) * darea (A 1) (A 2) (A 4) = 0 := by
  simp [darea, cross, PiLp.sub_apply]; ring

/-! ### Key step: the `q` values are pairwise distinct

If `q d = q e`, then for any other two indices `i, j` the points `A d`, `A e`
have the same distance from the line `A i A j`; applying this to the three
lines through three other points yields a contradiction with the hypothesis
that no three points are collinear. -/

/-- From equal distances to a line: either `A d A e` is parallel to the line,
or the midpoint of `A d A e` lies on it. -/
lemma par_or_mid {A : Fin 5 → Pt} {i j d e : Fin 5}
    (h : |darea (A i) (A j) (A d)| = |darea (A i) (A j) (A e)|) :
    cross (A j - A i) (A e - A d) = 0 ∨ cross (A j - A i) (A e + A d - (2 : ℝ) • A i) = 0 := by
  rcases abs_eq_abs.mp h with h1 | h1
  · left
    have hid : cross (A j - A i) (A e - A d) =
        darea (A i) (A j) (A e) - darea (A i) (A j) (A d) := by
      simp [cross, darea, PiLp.sub_apply]; ring
    rw [hid, h1, sub_self]
  · right
    have hid : cross (A j - A i) (A e + A d - (2 : ℝ) • A i) =
        darea (A i) (A j) (A e) + darea (A i) (A j) (A d) := by
      simp [cross, darea, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply]
      ring
    rw [hid]
    linarith [h1]

/-- Two "parallel" conditions sharing an index give three collinear points. -/
lemma kill_par {A : Fin 5 → Pt} {i j k d e : Fin 5}
    (hcoll : ∀ i j k : Fin 5, i ≠ j → j ≠ k → i ≠ k → darea (A i) (A j) (A k) ≠ 0)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (hid : i ≠ d) (hie : i ≠ e) (hde : d ≠ e)
    (h1 : cross (A j - A i) (A e - A d) = 0) (h2 : cross (A k - A i) (A e - A d) = 0) :
    False := by
  have hde' : A e - A d ≠ 0 := by
    intro hv
    have h2' : A e = A d := sub_eq_zero.mp hv
    have h0 : darea (A i) (A d) (A e) = 0 := by
      rw [h2']
      simp only [darea, cross, PiLp.sub_apply]
      ring
    exact hcoll i d e hid hde hie h0
  have h3 := cross_parallel_trans h1 h2 hde'
  exact hcoll i j k hij hjk hik h3

/-- Two "midpoint on line" conditions sharing an index give three collinear
points. -/
lemma kill_mid {A : Fin 5 → Pt} {i j k d e : Fin 5}
    (hcoll : ∀ i j k : Fin 5, i ≠ j → j ≠ k → i ≠ k → darea (A i) (A j) (A k) ≠ 0)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (hid : i ≠ d) (hie : i ≠ e) (hde : d ≠ e)
    (h1 : cross (A j - A i) (A e + A d - (2 : ℝ) • A i) = 0)
    (h2 : cross (A k - A i) (A e + A d - (2 : ℝ) • A i) = 0) : False := by
  by_cases hw : A e + A d - (2 : ℝ) • A i = 0
  · have hsum : A e + A d = (2 : ℝ) • A i := sub_eq_zero.mp hw
    have hvec : A e - A i = A i - A d := by
      apply Pt_ext
      intro t
      have ht : (A e + A d) t = ((2 : ℝ) • A i) t := by rw [hsum]
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, PiLp.sub_apply] at ht ⊢
      linarith
    have h0 : darea (A i) (A d) (A e) = 0 := by
      simp only [darea, cross, hvec, PiLp.sub_apply]
      ring
    exact hcoll i d e hid hde hie h0
  · have h3 := cross_parallel_trans h1 h2 hw
    exact hcoll i j k hij hjk hik h3

/-- The `q` values are pairwise distinct. -/
lemma q_ne_of_ne {A : Fin 5 → Pt} {q : Fin 5 → ℝ}
    (hcoll : ∀ i j k : Fin 5, i ≠ j → j ≠ k → i ≠ k → darea (A i) (A j) (A k) ≠ 0)
    (harea : ∀ i j k : Fin 5, i ≠ j → j ≠ k → i ≠ k →
      |darea (A i) (A j) (A k)| = q i + q j + q k)
    {d e : Fin 5} (hde : d ≠ e) : q d ≠ q e := by
  intro hqe
  have hcard : (Finset.univ \ {d, e} : Finset (Fin 5)).card = 3 := by
    have h1 : ({d, e} : Finset (Fin 5)).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp [hde]), Finset.card_singleton]
    rw [Finset.card_sdiff, Finset.card_univ, Fintype.card_fin, Finset.inter_univ, h1]
  obtain ⟨a, b, c, hab, hac, hbc, hcomp⟩ := Finset.card_eq_three.mp hcard
  have ha2 : a ∈ (Finset.univ \ {d, e} : Finset (Fin 5)) := by rw [hcomp]; simp
  have hb2 : b ∈ (Finset.univ \ {d, e} : Finset (Fin 5)) := by rw [hcomp]; simp
  have hc2 : c ∈ (Finset.univ \ {d, e} : Finset (Fin 5)) := by rw [hcomp]; simp
  simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or,
    Finset.mem_univ, true_and] at ha2 hb2 hc2
  obtain ⟨had, hae⟩ := ha2
  obtain ⟨hbd, hbe⟩ := hb2
  obtain ⟨hcd, hce⟩ := hc2
  have eab : |darea (A a) (A b) (A d)| = |darea (A a) (A b) (A e)| := by
    rw [harea a b d hab hbd had, harea a b e hab hbe hae, hqe]
  have eac : |darea (A a) (A c) (A d)| = |darea (A a) (A c) (A e)| := by
    rw [harea a c d hac hcd had, harea a c e hac hce hae, hqe]
  have ebc : |darea (A b) (A c) (A d)| = |darea (A b) (A c) (A e)| := by
    rw [harea b c d hbc hcd hbd, harea b c e hbc hce hbe, hqe]
  rcases par_or_mid eab with hpab | hmab <;>
  rcases par_or_mid eac with hpac | hmac <;>
  rcases par_or_mid ebc with hpbc | hmbc
  · exact kill_par hcoll hab hbc hac had hae hde hpab hpac
  · exact kill_par hcoll hab hbc hac had hae hde hpab hpac
  · exact kill_par hcoll (Ne.symm hab) hac hbc hbd hbe hde
      (by rw [cross_neg_left, hpab, neg_zero]) hpbc
  · exact kill_mid hcoll (Ne.symm hac) hab (Ne.symm hbc) hcd hce hde
      (by rw [mid_flip, hmac, neg_zero]) (by rw [mid_flip, hmbc, neg_zero])
  · exact kill_par hcoll (Ne.symm hac) hab (Ne.symm hbc) hcd hce hde
      (by rw [cross_neg_left, hpac, neg_zero]) (by rw [cross_neg_left, hpbc, neg_zero])
  · exact kill_mid hcoll (Ne.symm hab) hac hbc hbd hbe hde
      (by rw [mid_flip, hmab, neg_zero]) hmbc
  · exact kill_mid hcoll hab hbc hac had hae hde hmab hmac
  · exact kill_mid hcoll hab hbc hac had hae hde hmab hmac

/-! ### The classification

Any five points in general position contain one of the following
configurations, each of which forces two of the `q` values to coincide
(contradicting `q_ne_of_ne`):

* (C1) two convex quadrilaterals on `{a,b,c,d}` and `{a,b,c,e}` sharing the
  cyclic triple `a b c` (the convex pentagon case), giving `q d = q e`;
* (C2) two points strictly inside the same triangle (the triangular hull
  case), giving `q d = q e`;
* (C3) two convex quadrilaterals on `{a,b,c,d}` and `{a,b,e,d}` sharing the
  diagonal `b d` (the quadrilateral hull with an interior point case),
  giving `q c = q e`. -/

/-! ### The finite sign classification

The combinatorial heart of the classification: the ten `darea` signs of five
points in general position satisfy the five Plücker sign constraints and are
"acyclic" (some directed line has all remaining points strictly on its left);
a finite check over all `2^10` sign assignments shows that one of three
configurations must occur, each of which forces two `q`-values to coincide. -/

/-- The ten increasing triples of `Fin 5`, in lexicographic order. -/
def T : Fin 10 → Fin 5 × Fin 5 × Fin 5 :=
  ![((0 : Fin 5), (1 : Fin 5), (2 : Fin 5)), ((0 : Fin 5), (1 : Fin 5), (3 : Fin 5)),
    ((0 : Fin 5), (1 : Fin 5), (4 : Fin 5)), ((0 : Fin 5), (2 : Fin 5), (3 : Fin 5)),
    ((0 : Fin 5), (2 : Fin 5), (4 : Fin 5)), ((0 : Fin 5), (3 : Fin 5), (4 : Fin 5)),
    ((1 : Fin 5), (2 : Fin 5), (3 : Fin 5)), ((1 : Fin 5), (2 : Fin 5), (4 : Fin 5)),
    ((1 : Fin 5), (3 : Fin 5), (4 : Fin 5)), ((2 : Fin 5), (3 : Fin 5), (4 : Fin 5))]

/-- The index in `Fin 10` of the increasing rearrangement of `(i, j, k)`
(meaningful when the three are pairwise distinct). -/
def tidx (i j k : Fin 5) : Fin 10 :=
  let x := min (min i.val j.val) k.val
  let z := max (max i.val j.val) k.val
  let y := i.val + j.val + k.val - x - z
  ⟨if x = 0 then
     if y = 1 then (if z = 2 then 0 else if z = 3 then 1 else 2)
     else if y = 2 then (if z = 3 then 3 else 4)
     else 5
   else if x = 1 then
     if y = 2 then (if z = 3 then 6 else 7)
     else 8
   else 9, by split_ifs <;> decide⟩

/-- `true` iff the permutation taking the increasing rearrangement of
`(i, j, k)` to `(i, j, k)` is even (meaningful when pairwise distinct). -/
def teven (i j k : Fin 5) : Bool :=
  decide ((i.val ≤ j.val ∧ j.val ≤ k.val) ∨ (j.val ≤ k.val ∧ k.val ≤ i.val) ∨
    (k.val ≤ i.val ∧ i.val ≤ j.val))

/-- The sign of `darea` of a triple, read off from a sign assignment `s`
on the ten increasing triples. -/
def bit (s : Fin 10 → Bool) (i j k : Fin 5) : Bool :=
  if teven i j k then s (tidx i j k) else !s (tidx i j k)

/-- Boolean form of `ConvQuad`: the four triangles are consistently oriented. -/
def quadB (s : Fin 10 → Bool) (a b c d : Fin 5) : Bool :=
  (bit s a b c == bit s b c d) && (bit s b c d == bit s c d a) &&
  (bit s c d a == bit s d a b)

/-- Boolean form of `Inside`. -/
def insideB (s : Fin 10 → Bool) (x a b c : Fin 5) : Bool :=
  (bit s a b c == bit s x b c) && (bit s a b c == bit s a x c) &&
  (bit s a b c == bit s a b x)

/-- Boolean form of a three-term Plücker relation `t₁ - t₂ + t₃ = 0`:
the forbidden pattern is `t₁, t₃` of one sign and `t₂` of the other. -/
def relB (s1 s2 s3 : Bool) : Bool := (s1 != s3) || (s1 == s2)

/-- The five Plücker sign constraints, as a Bool. -/
def pluckerBB (s : Fin 10 → Bool) : Bool :=
  relB (bit s 0 1 2 == bit s 0 3 4) (bit s 0 1 3 == bit s 0 2 4)
    (bit s 0 1 4 == bit s 0 2 3) &&
  relB (bit s 0 1 2 == bit s 1 3 4) (bit s 0 1 3 == bit s 1 2 4)
    (bit s 0 1 4 == bit s 1 2 3) &&
  relB (bit s 0 1 2 == bit s 2 3 4) (bit s 0 2 3 == bit s 1 2 4)
    (bit s 0 2 4 == bit s 1 2 3) &&
  relB (bit s 0 1 3 == bit s 2 3 4) (bit s 0 2 3 == bit s 1 3 4)
    (bit s 0 3 4 == bit s 1 2 3) &&
  relB (bit s 0 1 4 == bit s 2 3 4) (bit s 0 2 4 == bit s 1 3 4)
    (bit s 0 3 4 == bit s 1 2 4)

/-- Acyclicity, as a Bool: some directed line has all remaining points
strictly on its left. -/
def acycBB (s : Fin 10 → Bool) : Bool :=
  (List.finRange 5).any fun i => (List.finRange 5).any fun j =>
    (i != j) && (List.finRange 5).all fun k => (k == i) || (k == j) || bit s i j k

/-- Five pairwise distinct indices, as a Bool. -/
def dist5B (a b c d e : Fin 5) : Bool :=
  (a != b) && (a != c) && (a != d) && (a != e) && (b != c) && (b != d) && (b != e) &&
  (c != d) && (c != e) && (d != e)

/-- Two convex quadrilaterals sharing the cyclic triple `a b c`, as a Bool. -/
def C1B (s : Fin 10 → Bool) : Bool :=
  (List.finRange 5).any fun a => (List.finRange 5).any fun b =>
  (List.finRange 5).any fun c => (List.finRange 5).any fun d =>
  (List.finRange 5).any fun e =>
    dist5B a b c d e && quadB s a b c d && quadB s a b c e

/-- Two points strictly inside the same triangle, as a Bool. -/
def C2B (s : Fin 10 → Bool) : Bool :=
  (List.finRange 5).any fun a => (List.finRange 5).any fun b =>
  (List.finRange 5).any fun c => (List.finRange 5).any fun d =>
  (List.finRange 5).any fun e =>
    dist5B a b c d e && insideB s d a b c && insideB s e a b c

/-- Two convex quadrilaterals sharing the diagonal `b d`, as a Bool. -/
def C3B (s : Fin 10 → Bool) : Bool :=
  (List.finRange 5).any fun a => (List.finRange 5).any fun b =>
  (List.finRange 5).any fun c => (List.finRange 5).any fun d =>
  (List.finRange 5).any fun e =>
    dist5B a b c d e && quadB s a b c d && quadB s a b e d

/-! ### Packing sign assignments as natural numbers for the finite check

Kernel evaluation of the classification over all `2^10` assignments is only
feasible when reading a sign is a cheap `Nat` operation, so assignments are
packed into natural numbers below `2^10` and unpacked via `Nat.testBit`. -/

/-- Unpack a natural number into a sign assignment: the `i`-th bit. -/
def unpack (n : Nat) (i : Fin 10) : Bool := Nat.testBit n i.val

/-- Pack a sign assignment into a natural number below `2^10` (Horner form). -/
def pack (s : Fin 10 → Bool) : Nat :=
  (s 0).toNat + 2 * ((s 1).toNat + 2 * ((s 2).toNat + 2 * ((s 3).toNat + 2 * ((s 4).toNat +
    2 * ((s 5).toNat + 2 * ((s 6).toNat + 2 * ((s 7).toNat + 2 * ((s 8).toNat +
    2 * (s 9).toNat))))))))

lemma pack_lt (s : Fin 10 → Bool) : pack s < 1024 := by
  have h0 : (s 0).toNat ≤ 1 := Bool.toNat_le _
  have h1 : (s 1).toNat ≤ 1 := Bool.toNat_le _
  have h2 : (s 2).toNat ≤ 1 := Bool.toNat_le _
  have h3 : (s 3).toNat ≤ 1 := Bool.toNat_le _
  have h4 : (s 4).toNat ≤ 1 := Bool.toNat_le _
  have h5 : (s 5).toNat ≤ 1 := Bool.toNat_le _
  have h6 : (s 6).toNat ≤ 1 := Bool.toNat_le _
  have h7 : (s 7).toNat ≤ 1 := Bool.toNat_le _
  have h8 : (s 8).toNat ≤ 1 := Bool.toNat_le _
  have h9 : (s 9).toNat ≤ 1 := Bool.toNat_le _
  simp only [pack]
  omega

lemma testBit_pack0 (b : Bool) (m : Nat) : Nat.testBit (b.toNat + 2 * m) 0 = b := by
  have h1 : (b.toNat + 2 * m) % 2 = b.toNat % 2 := by omega
  have h2 := Nat.testBit_zero (b.toNat + 2 * m)
  rw [h1] at h2
  rw [h2]
  cases b <;> decide

lemma testBit_packS (b : Bool) (m i : Nat) :
    Nat.testBit (b.toNat + 2 * m) (i + 1) = Nat.testBit m i := by
  have h1 : (b.toNat + 2 * m) / 2 = m := by
    have hb : b.toNat ≤ 1 := Bool.toNat_le b
    omega
  have h2 := Nat.testBit_succ (b.toNat + 2 * m) i
  rw [h1] at h2
  exact h2

lemma unpack_pack (s : Fin 10 → Bool) : unpack (pack s) = s := by
  funext i
  fin_cases i <;> simp only [unpack, pack]
  · exact testBit_pack0 (s 0) _
  · exact (testBit_packS (s 0) _ 0).trans (testBit_pack0 (s 1) _)
  · exact (testBit_packS (s 0) _ 1).trans ((testBit_packS (s 1) _ 0).trans
      (testBit_pack0 (s 2) _))
  · exact (testBit_packS (s 0) _ 2).trans ((testBit_packS (s 1) _ 1).trans
      ((testBit_packS (s 2) _ 0).trans (testBit_pack0 (s 3) _)))
  · exact (testBit_packS (s 0) _ 3).trans ((testBit_packS (s 1) _ 2).trans
      ((testBit_packS (s 2) _ 1).trans ((testBit_packS (s 3) _ 0).trans
      (testBit_pack0 (s 4) _))))
  · exact (testBit_packS (s 0) _ 4).trans ((testBit_packS (s 1) _ 3).trans
      ((testBit_packS (s 2) _ 2).trans ((testBit_packS (s 3) _ 1).trans
      ((testBit_packS (s 4) _ 0).trans (testBit_pack0 (s 5) _)))))
  · exact (testBit_packS (s 0) _ 5).trans ((testBit_packS (s 1) _ 4).trans
      ((testBit_packS (s 2) _ 3).trans ((testBit_packS (s 3) _ 2).trans
      ((testBit_packS (s 4) _ 1).trans ((testBit_packS (s 5) _ 0).trans
      (testBit_pack0 (s 6) _))))))
  · exact (testBit_packS (s 0) _ 6).trans ((testBit_packS (s 1) _ 5).trans
      ((testBit_packS (s 2) _ 4).trans ((testBit_packS (s 3) _ 3).trans
      ((testBit_packS (s 4) _ 2).trans ((testBit_packS (s 5) _ 1).trans
      ((testBit_packS (s 6) _ 0).trans (testBit_pack0 (s 7) _)))))))
  · exact (testBit_packS (s 0) _ 7).trans ((testBit_packS (s 1) _ 6).trans
      ((testBit_packS (s 2) _ 5).trans ((testBit_packS (s 3) _ 4).trans
      ((testBit_packS (s 4) _ 3).trans ((testBit_packS (s 5) _ 2).trans
      ((testBit_packS (s 6) _ 1).trans ((testBit_packS (s 7) _ 0).trans
      (testBit_pack0 (s 8) _))))))))
  · exact (testBit_packS (s 0) _ 8).trans ((testBit_packS (s 1) _ 7).trans
      ((testBit_packS (s 2) _ 6).trans ((testBit_packS (s 3) _ 5).trans
      ((testBit_packS (s 4) _ 4).trans ((testBit_packS (s 5) _ 3).trans
      ((testBit_packS (s 6) _ 2).trans ((testBit_packS (s 7) _ 1).trans
      ((testBit_packS (s 8) _ 0).trans (testBit_pack0 (s 9) 0)))))))))

/-- The Boolean checked over all packed sign assignments. -/
def checkSigns (n : Nat) : Bool :=
  !(pluckerBB (unpack n)) || !(acycBB (unpack n)) ||
    (C1B (unpack n) || C2B (unpack n) || C3B (unpack n))

/-- The finite classification, checked over all `2^10` packed sign
assignments.  The check is split into chunks of `128` assignments to bound
the memory needed by each kernel reduction. -/
lemma sign_classify_chunk0 :
    (List.range 128).all (fun k => checkSigns (128 * 0 + k)) = true := by
  decide +kernel

lemma sign_classify_chunk1 :
    (List.range 128).all (fun k => checkSigns (128 * 1 + k)) = true := by
  decide +kernel

lemma sign_classify_chunk2 :
    (List.range 128).all (fun k => checkSigns (128 * 2 + k)) = true := by
  decide +kernel

lemma sign_classify_chunk3 :
    (List.range 128).all (fun k => checkSigns (128 * 3 + k)) = true := by
  decide +kernel

lemma sign_classify_chunk4 :
    (List.range 128).all (fun k => checkSigns (128 * 4 + k)) = true := by
  decide +kernel

lemma sign_classify_chunk5 :
    (List.range 128).all (fun k => checkSigns (128 * 5 + k)) = true := by
  decide +kernel

lemma sign_classify_chunk6 :
    (List.range 128).all (fun k => checkSigns (128 * 6 + k)) = true := by
  decide +kernel

lemma sign_classify_chunk7 :
    (List.range 128).all (fun k => checkSigns (128 * 7 + k)) = true := by
  decide +kernel

theorem sign_classify_packed : (List.range 1024).all checkSigns = true := by
  apply List.all_eq_true.mpr
  intro n hn
  have hn' : n < 1024 := List.mem_range.mp hn
  have hq : n / 128 < 8 := by omega
  have hr : n % 128 < 128 := by omega
  have he : 128 * (n / 128) + n % 128 = n := by omega
  have hsel : ∀ q, q < 8 → checkSigns (128 * q + n % 128) = true := by
    intro q hq'
    interval_cases q
    · exact List.all_eq_true.mp sign_classify_chunk0 _ (List.mem_range.mpr hr)
    · exact List.all_eq_true.mp sign_classify_chunk1 _ (List.mem_range.mpr hr)
    · exact List.all_eq_true.mp sign_classify_chunk2 _ (List.mem_range.mpr hr)
    · exact List.all_eq_true.mp sign_classify_chunk3 _ (List.mem_range.mpr hr)
    · exact List.all_eq_true.mp sign_classify_chunk4 _ (List.mem_range.mpr hr)
    · exact List.all_eq_true.mp sign_classify_chunk5 _ (List.mem_range.mpr hr)
    · exact List.all_eq_true.mp sign_classify_chunk6 _ (List.mem_range.mpr hr)
    · exact List.all_eq_true.mp sign_classify_chunk7 _ (List.mem_range.mpr hr)
  have h := hsel (n / 128) hq
  rwa [he] at h

/-- The finite classification, checked over all `2^10` sign assignments. -/
theorem sign_classify_bool :
    ∀ s ∈ (Finset.univ : Finset (Fin 10 → Bool)),
      (!(pluckerBB s) || !(acycBB s) || (C1B s || C2B s || C3B s)) = true := by
  intro s _
  have h : (!(pluckerBB (unpack (pack s))) || !(acycBB (unpack (pack s))) ||
      (C1B (unpack (pack s)) || C2B (unpack (pack s)) || C3B (unpack (pack s)))) = true :=
    (List.all_eq_true.mp sign_classify_packed) (pack s) (List.mem_range.mpr (pack_lt s))
  rwa [unpack_pack] at h

/-- `Prop` form of `relB`. -/
@[reducible]
def relC (s1 s2 s3 : Bool) : Prop := s1 = s3 → s1 = s2

/-- `Prop` form of the Plücker sign constraints. -/
def pluckerB (s : Fin 10 → Bool) : Prop :=
  ((((relC (bit s 0 1 2 == bit s 0 3 4) (bit s 0 1 3 == bit s 0 2 4)
      (bit s 0 1 4 == bit s 0 2 3) ∧
    relC (bit s 0 1 2 == bit s 1 3 4) (bit s 0 1 3 == bit s 1 2 4)
      (bit s 0 1 4 == bit s 1 2 3)) ∧
    relC (bit s 0 1 2 == bit s 2 3 4) (bit s 0 2 3 == bit s 1 2 4)
      (bit s 0 2 4 == bit s 1 2 3)) ∧
    relC (bit s 0 1 3 == bit s 2 3 4) (bit s 0 2 3 == bit s 1 3 4)
      (bit s 0 3 4 == bit s 1 2 3)) ∧
    relC (bit s 0 1 4 == bit s 2 3 4) (bit s 0 2 4 == bit s 1 3 4)
      (bit s 0 3 4 == bit s 1 2 4))

/-- `Prop` form of acyclicity. -/
def acycB (s : Fin 10 → Bool) : Prop :=
  ∃ i j : Fin 5, i ≠ j ∧ ∀ k : Fin 5, k ≠ i → k ≠ j → bit s i j k = true

/-- `Prop` form of five pairwise distinct indices. -/
@[reducible]
def dist5 (a b c d e : Fin 5) : Prop :=
  a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ a ≠ e ∧ b ≠ c ∧ b ≠ d ∧ b ≠ e ∧ c ≠ d ∧ c ≠ e ∧ d ≠ e

/-- `Prop` form of `C1B`. -/
@[reducible]
def C1 (s : Fin 10 → Bool) : Prop :=
  ∃ a b c d e : Fin 5, (dist5 a b c d e ∧ quadB s a b c d = true) ∧ quadB s a b c e = true

/-- `Prop` form of `C2B`. -/
@[reducible]
def C2 (s : Fin 10 → Bool) : Prop :=
  ∃ a b c d e : Fin 5, (dist5 a b c d e ∧ insideB s d a b c = true) ∧ insideB s e a b c = true

/-- `Prop` form of `C3B`. -/
@[reducible]
def C3 (s : Fin 10 → Bool) : Prop :=
  ∃ a b c d e : Fin 5, (dist5 a b c d e ∧ quadB s a b c d = true) ∧ quadB s a b e d = true

lemma relB_iff (s1 s2 s3 : Bool) : relB s1 s2 s3 = true ↔ relC s1 s2 s3 := by
  cases s1 <;> cases s2 <;> cases s3 <;> decide

lemma pluckerBB_iff (s : Fin 10 → Bool) : pluckerBB s = true ↔ pluckerB s := by
  simp only [pluckerBB, pluckerB, Bool.and_eq_true_iff, relB_iff]

lemma acycBB_iff (s : Fin 10 → Bool) : acycBB s = true ↔ acycB s := by
  simp only [acycBB, acycB, List.any_eq_true, List.all_eq_true, List.mem_finRange,
    Bool.and_eq_true_iff, Bool.or_eq_true_iff, bne_iff_ne, beq_iff_eq, true_and, true_implies]
  constructor
  · rintro ⟨i, j, hij, h⟩
    refine ⟨i, j, hij, fun k hki hkj => ?_⟩
    exact (h k).elim
      (fun h1 => h1.elim (fun h1i => absurd h1i hki) (fun h2j => absurd h2j hkj)) id
  · rintro ⟨i, j, hij, h⟩
    exact ⟨i, j, hij, fun k => by
      by_cases hki : k = i
      · exact Or.inl (Or.inl hki)
      · by_cases hkj : k = j
        · exact Or.inl (Or.inr hkj)
        · exact Or.inr (h k hki hkj)⟩

lemma dist5B_iff (a b c d e : Fin 5) : dist5B a b c d e = true ↔ dist5 a b c d e := by
  simp only [dist5B, dist5, Bool.and_eq_true_iff, bne_iff_ne]
  tauto

lemma C1B_iff (s : Fin 10 → Bool) : C1B s = true ↔ C1 s := by
  simp only [C1B, C1, List.any_eq_true, List.mem_finRange, Bool.and_eq_true_iff, dist5B_iff,
    true_and]

lemma C2B_iff (s : Fin 10 → Bool) : C2B s = true ↔ C2 s := by
  simp only [C2B, C2, List.any_eq_true, List.mem_finRange, Bool.and_eq_true_iff, dist5B_iff,
    true_and]

lemma C3B_iff (s : Fin 10 → Bool) : C3B s = true ↔ C3 s := by
  simp only [C3B, C3, List.any_eq_true, List.mem_finRange, Bool.and_eq_true_iff, dist5B_iff,
    true_and]

/-- The finite classification in `Prop` form. -/
theorem sign_classify (s : Fin 10 → Bool) (hp : pluckerBB s = true) (ha : acycBB s = true) :
    C1B s = true ∨ C2B s = true ∨ C3B s = true := by
  have hs := sign_classify_bool s (Finset.mem_univ s)
  rw [hp, ha] at hs
  simp only [Bool.not_true, Bool.false_or] at hs
  rcases (Bool.or_eq_true_iff).mp hs with h12 | h3
  · rcases (Bool.or_eq_true_iff).mp h12 with h1 | h2
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr h3)

/-- The sign assignment of an actual configuration. -/
noncomputable def sgn (A : Fin 5 → Pt) (t : Fin 10) : Bool :=
  decide (0 < darea (A (T t).1) (A (T t).2.1) (A (T t).2.2))

lemma decide_pos_congr {x y : ℝ} (h : x = y) : decide (0 < x) = decide (0 < y) := by
  rw [h]

lemma decide_pos_neg {x : ℝ} (hx : x ≠ 0) : (!decide (0 < x)) = decide (0 < -x) := by
  rcases lt_or_gt_of_ne hx with h | h
  · have h1 : ¬ (0 < x) := by linarith
    have h2 : 0 < -x := by linarith
    simp [h1, h2]
  · have h1 : ¬ (0 < -x) := by linarith
    simp [h, h1]

/-- `bit (sgn A) i j k` computes the sign of `darea (A i) (A j) (A k)`. -/
lemma bit_eq {A : Fin 5 → Pt}
    (hcoll : ∀ i j k : Fin 5, i ≠ j → j ≠ k → i ≠ k → darea (A i) (A j) (A k) ≠ 0)
    (i j k : Fin 5) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    bit (sgn A) i j k = decide (0 < darea (A i) (A j) (A k)) := by
  fin_cases i <;> fin_cases j <;> fin_cases k
  · exact absurd rfl hij
  · exact absurd rfl hij
  · exact absurd rfl hij
  · exact absurd rfl hij
  · exact absurd rfl hij
  · exact absurd rfl hik
  · exact absurd rfl hjk
  · show decide (0 < darea (A 0) (A 1) (A 2)) =
      decide (0 < darea (A 0) (A 1) (A 2))
    exact decide_pos_congr rfl
  · show decide (0 < darea (A 0) (A 1) (A 3)) =
      decide (0 < darea (A 0) (A 1) (A 3))
    exact decide_pos_congr rfl
  · show decide (0 < darea (A 0) (A 1) (A 4)) =
      decide (0 < darea (A 0) (A 1) (A 4))
    exact decide_pos_congr rfl
  · exact absurd rfl hik
  · show (!decide (0 < darea (A 0) (A 1) (A 2))) =
      decide (0 < darea (A 0) (A 2) (A 1))
    exact (decide_pos_neg (hcoll _ _ _ (by decide) (by decide) (by decide))).trans
      (decide_pos_congr ((darea_swap32 _ _ _).symm))
  · exact absurd rfl hjk
  · show decide (0 < darea (A 0) (A 2) (A 3)) =
      decide (0 < darea (A 0) (A 2) (A 3))
    exact decide_pos_congr rfl
  · show decide (0 < darea (A 0) (A 2) (A 4)) =
      decide (0 < darea (A 0) (A 2) (A 4))
    exact decide_pos_congr rfl
  · exact absurd rfl hik
  · show (!decide (0 < darea (A 0) (A 1) (A 3))) =
      decide (0 < darea (A 0) (A 3) (A 1))
    exact (decide_pos_neg (hcoll _ _ _ (by decide) (by decide) (by decide))).trans
      (decide_pos_congr ((darea_swap32 _ _ _).symm))
  · show (!decide (0 < darea (A 0) (A 2) (A 3))) =
      decide (0 < darea (A 0) (A 3) (A 2))
    exact (decide_pos_neg (hcoll _ _ _ (by decide) (by decide) (by decide))).trans
      (decide_pos_congr ((darea_swap32 _ _ _).symm))
  · exact absurd rfl hjk
  · show decide (0 < darea (A 0) (A 3) (A 4)) =
      decide (0 < darea (A 0) (A 3) (A 4))
    exact decide_pos_congr rfl
  · exact absurd rfl hik
  · show (!decide (0 < darea (A 0) (A 1) (A 4))) =
      decide (0 < darea (A 0) (A 4) (A 1))
    exact (decide_pos_neg (hcoll _ _ _ (by decide) (by decide) (by decide))).trans
      (decide_pos_congr ((darea_swap32 _ _ _).symm))
  · show (!decide (0 < darea (A 0) (A 2) (A 4))) =
      decide (0 < darea (A 0) (A 4) (A 2))
    exact (decide_pos_neg (hcoll _ _ _ (by decide) (by decide) (by decide))).trans
      (decide_pos_congr ((darea_swap32 _ _ _).symm))
  · show (!decide (0 < darea (A 0) (A 3) (A 4))) =
      decide (0 < darea (A 0) (A 4) (A 3))
    exact (decide_pos_neg (hcoll _ _ _ (by decide) (by decide) (by decide))).trans
      (decide_pos_congr ((darea_swap32 _ _ _).symm))
  · exact absurd rfl hjk
  · exact absurd rfl hjk
  · exact absurd rfl hik
  · show (!decide (0 < darea (A 0) (A 1) (A 2))) =
      decide (0 < darea (A 1) (A 0) (A 2))
    exact (decide_pos_neg (hcoll _ _ _ (by decide) (by decide) (by decide))).trans
      (decide_pos_congr ((darea_swap21 _ _ _).symm))
  · show (!decide (0 < darea (A 0) (A 1) (A 3))) =
      decide (0 < darea (A 1) (A 0) (A 3))
    exact (decide_pos_neg (hcoll _ _ _ (by decide) (by decide) (by decide))).trans
      (decide_pos_congr ((darea_swap21 _ _ _).symm))
  · show (!decide (0 < darea (A 0) (A 1) (A 4))) =
      decide (0 < darea (A 1) (A 0) (A 4))
    exact (decide_pos_neg (hcoll _ _ _ (by decide) (by decide) (by decide))).trans
      (decide_pos_congr ((darea_swap21 _ _ _).symm))
  · exact absurd rfl hij
  · exact absurd rfl hij
  · exact absurd rfl hij
  · exact absurd rfl hij
  · exact absurd rfl hij
  · show decide (0 < darea (A 0) (A 1) (A 2)) =
      decide (0 < darea (A 1) (A 2) (A 0))
    exact decide_pos_congr (darea_rot _ _ _)
  · exact absurd rfl hik
  · exact absurd rfl hjk
  · show decide (0 < darea (A 1) (A 2) (A 3)) =
      decide (0 < darea (A 1) (A 2) (A 3))
    exact decide_pos_congr rfl
  · show decide (0 < darea (A 1) (A 2) (A 4)) =
      decide (0 < darea (A 1) (A 2) (A 4))
    exact decide_pos_congr rfl
  · show decide (0 < darea (A 0) (A 1) (A 3)) =
      decide (0 < darea (A 1) (A 3) (A 0))
    exact decide_pos_congr (darea_rot _ _ _)
  · exact absurd rfl hik
  · show (!decide (0 < darea (A 1) (A 2) (A 3))) =
      decide (0 < darea (A 1) (A 3) (A 2))
    exact (decide_pos_neg (hcoll _ _ _ (by decide) (by decide) (by decide))).trans
      (decide_pos_congr ((darea_swap32 _ _ _).symm))
  · exact absurd rfl hjk
  · show decide (0 < darea (A 1) (A 3) (A 4)) =
      decide (0 < darea (A 1) (A 3) (A 4))
    exact decide_pos_congr rfl
  · show decide (0 < darea (A 0) (A 1) (A 4)) =
      decide (0 < darea (A 1) (A 4) (A 0))
    exact decide_pos_congr (darea_rot _ _ _)
  · exact absurd rfl hik
  · show (!decide (0 < darea (A 1) (A 2) (A 4))) =
      decide (0 < darea (A 1) (A 4) (A 2))
    exact (decide_pos_neg (hcoll _ _ _ (by decide) (by decide) (by decide))).trans
      (decide_pos_congr ((darea_swap32 _ _ _).symm))
  · show (!decide (0 < darea (A 1) (A 3) (A 4))) =
      decide (0 < darea (A 1) (A 4) (A 3))
    exact (decide_pos_neg (hcoll _ _ _ (by decide) (by decide) (by decide))).trans
      (decide_pos_congr ((darea_swap32 _ _ _).symm))
  · exact absurd rfl hjk
  · exact absurd rfl hjk
  · show decide (0 < darea (A 0) (A 1) (A 2)) =
      decide (0 < darea (A 2) (A 0) (A 1))
    exact decide_pos_congr ((darea_rot _ _ _).trans (darea_rot _ _ _))
  · exact absurd rfl hik
  · show (!decide (0 < darea (A 0) (A 2) (A 3))) =
      decide (0 < darea (A 2) (A 0) (A 3))
    exact (decide_pos_neg (hcoll _ _ _ (by decide) (by decide) (by decide))).trans
      (decide_pos_congr ((darea_swap21 _ _ _).symm))
  · show (!decide (0 < darea (A 0) (A 2) (A 4))) =
      decide (0 < darea (A 2) (A 0) (A 4))
    exact (decide_pos_neg (hcoll _ _ _ (by decide) (by decide) (by decide))).trans
      (decide_pos_congr ((darea_swap21 _ _ _).symm))
  · show (!decide (0 < darea (A 0) (A 1) (A 2))) =
      decide (0 < darea (A 2) (A 1) (A 0))
    exact (decide_pos_neg (hcoll _ _ _ (by decide) (by decide) (by decide))).trans
      (decide_pos_congr ((darea_swap21 _ _ _).symm.trans ((darea_rot _ _ _).trans (darea_rot _ _ _))))
  · exact absurd rfl hjk
  · exact absurd rfl hik
  · show (!decide (0 < darea (A 1) (A 2) (A 3))) =
      decide (0 < darea (A 2) (A 1) (A 3))
    exact (decide_pos_neg (hcoll _ _ _ (by decide) (by decide) (by decide))).trans
      (decide_pos_congr ((darea_swap21 _ _ _).symm))
  · show (!decide (0 < darea (A 1) (A 2) (A 4))) =
      decide (0 < darea (A 2) (A 1) (A 4))
    exact (decide_pos_neg (hcoll _ _ _ (by decide) (by decide) (by decide))).trans
      (decide_pos_congr ((darea_swap21 _ _ _).symm))
  · exact absurd rfl hij
  · exact absurd rfl hij
  · exact absurd rfl hij
  · exact absurd rfl hij
  · exact absurd rfl hij
  · show decide (0 < darea (A 0) (A 2) (A 3)) =
      decide (0 < darea (A 2) (A 3) (A 0))
    exact decide_pos_congr (darea_rot _ _ _)
  · show decide (0 < darea (A 1) (A 2) (A 3)) =
      decide (0 < darea (A 2) (A 3) (A 1))
    exact decide_pos_congr (darea_rot _ _ _)
  · exact absurd rfl hik
  · exact absurd rfl hjk
  · show decide (0 < darea (A 2) (A 3) (A 4)) =
      decide (0 < darea (A 2) (A 3) (A 4))
    exact decide_pos_congr rfl
  · show decide (0 < darea (A 0) (A 2) (A 4)) =
      decide (0 < darea (A 2) (A 4) (A 0))
    exact decide_pos_congr (darea_rot _ _ _)
  · show decide (0 < darea (A 1) (A 2) (A 4)) =
      decide (0 < darea (A 2) (A 4) (A 1))
    exact decide_pos_congr (darea_rot _ _ _)
  · exact absurd rfl hik
  · show (!decide (0 < darea (A 2) (A 3) (A 4))) =
      decide (0 < darea (A 2) (A 4) (A 3))
    exact (decide_pos_neg (hcoll _ _ _ (by decide) (by decide) (by decide))).trans
      (decide_pos_congr ((darea_swap32 _ _ _).symm))
  · exact absurd rfl hjk
  · exact absurd rfl hjk
  · show decide (0 < darea (A 0) (A 1) (A 3)) =
      decide (0 < darea (A 3) (A 0) (A 1))
    exact decide_pos_congr ((darea_rot _ _ _).trans (darea_rot _ _ _))
  · show decide (0 < darea (A 0) (A 2) (A 3)) =
      decide (0 < darea (A 3) (A 0) (A 2))
    exact decide_pos_congr ((darea_rot _ _ _).trans (darea_rot _ _ _))
  · exact absurd rfl hik
  · show (!decide (0 < darea (A 0) (A 3) (A 4))) =
      decide (0 < darea (A 3) (A 0) (A 4))
    exact (decide_pos_neg (hcoll _ _ _ (by decide) (by decide) (by decide))).trans
      (decide_pos_congr ((darea_swap21 _ _ _).symm))
  · show (!decide (0 < darea (A 0) (A 1) (A 3))) =
      decide (0 < darea (A 3) (A 1) (A 0))
    exact (decide_pos_neg (hcoll _ _ _ (by decide) (by decide) (by decide))).trans
      (decide_pos_congr ((darea_swap21 _ _ _).symm.trans ((darea_rot _ _ _).trans (darea_rot _ _ _))))
  · exact absurd rfl hjk
  · show decide (0 < darea (A 1) (A 2) (A 3)) =
      decide (0 < darea (A 3) (A 1) (A 2))
    exact decide_pos_congr ((darea_rot _ _ _).trans (darea_rot _ _ _))
  · exact absurd rfl hik
  · show (!decide (0 < darea (A 1) (A 3) (A 4))) =
      decide (0 < darea (A 3) (A 1) (A 4))
    exact (decide_pos_neg (hcoll _ _ _ (by decide) (by decide) (by decide))).trans
      (decide_pos_congr ((darea_swap21 _ _ _).symm))
  · show (!decide (0 < darea (A 0) (A 2) (A 3))) =
      decide (0 < darea (A 3) (A 2) (A 0))
    exact (decide_pos_neg (hcoll _ _ _ (by decide) (by decide) (by decide))).trans
      (decide_pos_congr ((darea_swap21 _ _ _).symm.trans ((darea_rot _ _ _).trans (darea_rot _ _ _))))
  · show (!decide (0 < darea (A 1) (A 2) (A 3))) =
      decide (0 < darea (A 3) (A 2) (A 1))
    exact (decide_pos_neg (hcoll _ _ _ (by decide) (by decide) (by decide))).trans
      (decide_pos_congr ((darea_swap21 _ _ _).symm.trans ((darea_rot _ _ _).trans (darea_rot _ _ _))))
  · exact absurd rfl hjk
  · exact absurd rfl hik
  · show (!decide (0 < darea (A 2) (A 3) (A 4))) =
      decide (0 < darea (A 3) (A 2) (A 4))
    exact (decide_pos_neg (hcoll _ _ _ (by decide) (by decide) (by decide))).trans
      (decide_pos_congr ((darea_swap21 _ _ _).symm))
  · exact absurd rfl hij
  · exact absurd rfl hij
  · exact absurd rfl hij
  · exact absurd rfl hij
  · exact absurd rfl hij
  · show decide (0 < darea (A 0) (A 3) (A 4)) =
      decide (0 < darea (A 3) (A 4) (A 0))
    exact decide_pos_congr (darea_rot _ _ _)
  · show decide (0 < darea (A 1) (A 3) (A 4)) =
      decide (0 < darea (A 3) (A 4) (A 1))
    exact decide_pos_congr (darea_rot _ _ _)
  · show decide (0 < darea (A 2) (A 3) (A 4)) =
      decide (0 < darea (A 3) (A 4) (A 2))
    exact decide_pos_congr (darea_rot _ _ _)
  · exact absurd rfl hik
  · exact absurd rfl hjk
  · exact absurd rfl hjk
  · show decide (0 < darea (A 0) (A 1) (A 4)) =
      decide (0 < darea (A 4) (A 0) (A 1))
    exact decide_pos_congr ((darea_rot _ _ _).trans (darea_rot _ _ _))
  · show decide (0 < darea (A 0) (A 2) (A 4)) =
      decide (0 < darea (A 4) (A 0) (A 2))
    exact decide_pos_congr ((darea_rot _ _ _).trans (darea_rot _ _ _))
  · show decide (0 < darea (A 0) (A 3) (A 4)) =
      decide (0 < darea (A 4) (A 0) (A 3))
    exact decide_pos_congr ((darea_rot _ _ _).trans (darea_rot _ _ _))
  · exact absurd rfl hik
  · show (!decide (0 < darea (A 0) (A 1) (A 4))) =
      decide (0 < darea (A 4) (A 1) (A 0))
    exact (decide_pos_neg (hcoll _ _ _ (by decide) (by decide) (by decide))).trans
      (decide_pos_congr ((darea_swap21 _ _ _).symm.trans ((darea_rot _ _ _).trans (darea_rot _ _ _))))
  · exact absurd rfl hjk
  · show decide (0 < darea (A 1) (A 2) (A 4)) =
      decide (0 < darea (A 4) (A 1) (A 2))
    exact decide_pos_congr ((darea_rot _ _ _).trans (darea_rot _ _ _))
  · show decide (0 < darea (A 1) (A 3) (A 4)) =
      decide (0 < darea (A 4) (A 1) (A 3))
    exact decide_pos_congr ((darea_rot _ _ _).trans (darea_rot _ _ _))
  · exact absurd rfl hik
  · show (!decide (0 < darea (A 0) (A 2) (A 4))) =
      decide (0 < darea (A 4) (A 2) (A 0))
    exact (decide_pos_neg (hcoll _ _ _ (by decide) (by decide) (by decide))).trans
      (decide_pos_congr ((darea_swap21 _ _ _).symm.trans ((darea_rot _ _ _).trans (darea_rot _ _ _))))
  · show (!decide (0 < darea (A 1) (A 2) (A 4))) =
      decide (0 < darea (A 4) (A 2) (A 1))
    exact (decide_pos_neg (hcoll _ _ _ (by decide) (by decide) (by decide))).trans
      (decide_pos_congr ((darea_swap21 _ _ _).symm.trans ((darea_rot _ _ _).trans (darea_rot _ _ _))))
  · exact absurd rfl hjk
  · show decide (0 < darea (A 2) (A 3) (A 4)) =
      decide (0 < darea (A 4) (A 2) (A 3))
    exact decide_pos_congr ((darea_rot _ _ _).trans (darea_rot _ _ _))
  · exact absurd rfl hik
  · show (!decide (0 < darea (A 0) (A 3) (A 4))) =
      decide (0 < darea (A 4) (A 3) (A 0))
    exact (decide_pos_neg (hcoll _ _ _ (by decide) (by decide) (by decide))).trans
      (decide_pos_congr ((darea_swap21 _ _ _).symm.trans ((darea_rot _ _ _).trans (darea_rot _ _ _))))
  · show (!decide (0 < darea (A 1) (A 3) (A 4))) =
      decide (0 < darea (A 4) (A 3) (A 1))
    exact (decide_pos_neg (hcoll _ _ _ (by decide) (by decide) (by decide))).trans
      (decide_pos_congr ((darea_swap21 _ _ _).symm.trans ((darea_rot _ _ _).trans (darea_rot _ _ _))))
  · show (!decide (0 < darea (A 2) (A 3) (A 4))) =
      decide (0 < darea (A 4) (A 3) (A 2))
    exact (decide_pos_neg (hcoll _ _ _ (by decide) (by decide) (by decide))).trans
      (decide_pos_congr ((darea_swap21 _ _ _).symm.trans ((darea_rot _ _ _).trans (darea_rot _ _ _))))
  · exact absurd rfl hjk
  · exact absurd rfl hik
  · exact absurd rfl hij
  · exact absurd rfl hij
  · exact absurd rfl hij
  · exact absurd rfl hij
  · exact absurd rfl hij

/-- Two nonzero reals of the same sign have a positive product. -/
lemma mul_pos_of_decide_eq {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : decide (0 < x) = decide (0 < y)) : 0 < x * y := by
  have h' : (0 < x) ↔ (0 < y) := decide_eq_decide.mp h
  rcases lt_or_gt_of_ne hx with h1 | h1 <;> rcases lt_or_gt_of_ne hy with h2 | h2
  · exact mul_pos_of_neg_of_neg h1 h2
  · exact absurd (h'.mpr h2) (by linarith)
  · exact absurd (h'.mp h1) (by linarith)
  · exact mul_pos h1 h2

/-- Decoding `quadB` into `ConvQuad`. -/
lemma quadB_to_ConvQuad {A : Fin 5 → Pt}
    (hcoll : ∀ i j k : Fin 5, i ≠ j → j ≠ k → i ≠ k → darea (A i) (A j) (A k) ≠ 0)
    {a b c d : Fin 5}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (h : quadB (sgn A) a b c d = true) : ConvQuad A a b c d := by
  simp only [quadB, Bool.and_eq_true_iff, beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  rw [bit_eq hcoll a b c hab hbc hac, bit_eq hcoll b c d hbc hcd hbd] at h1
  rw [bit_eq hcoll b c d hbc hcd hbd,
    bit_eq hcoll c d a hcd (Ne.symm had) (Ne.symm hac)] at h2
  rw [bit_eq hcoll c d a hcd (Ne.symm had) (Ne.symm hac),
    bit_eq hcoll d a b (Ne.symm had) hab (Ne.symm hbd)] at h3
  exact ⟨mul_pos_of_decide_eq (hcoll a b c hab hbc hac) (hcoll b c d hbc hcd hbd) h1,
    mul_pos_of_decide_eq (hcoll b c d hbc hcd hbd)
      (hcoll c d a hcd (Ne.symm had) (Ne.symm hac)) h2,
    mul_pos_of_decide_eq (hcoll c d a hcd (Ne.symm had) (Ne.symm hac))
      (hcoll d a b (Ne.symm had) hab (Ne.symm hbd)) h3⟩

/-- Decoding `insideB` into `Inside`. -/
lemma insideB_to_Inside {A : Fin 5 → Pt}
    (hcoll : ∀ i j k : Fin 5, i ≠ j → j ≠ k → i ≠ k → darea (A i) (A j) (A k) ≠ 0)
    {x a b c : Fin 5}
    (hxa : x ≠ a) (hxb : x ≠ b) (hxc : x ≠ c) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (h : insideB (sgn A) x a b c = true) : Inside A x a b c := by
  simp only [insideB, Bool.and_eq_true_iff, beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  rw [bit_eq hcoll a b c hab hbc hac, bit_eq hcoll x b c hxb hbc hxc] at h1
  rw [bit_eq hcoll a b c hab hbc hac, bit_eq hcoll a x c (Ne.symm hxa) hxc hac] at h2
  rw [bit_eq hcoll a b c hab hbc hac, bit_eq hcoll a b x hab (Ne.symm hxb) (Ne.symm hxa)] at h3
  exact ⟨mul_pos_of_decide_eq (hcoll a b c hab hbc hac) (hcoll x b c hxb hbc hxc) h1,
    mul_pos_of_decide_eq (hcoll a b c hab hbc hac)
      (hcoll a x c (Ne.symm hxa) hxc hac) h2,
    mul_pos_of_decide_eq (hcoll a b c hab hbc hac)
      (hcoll a b x hab (Ne.symm hxb) (Ne.symm hxa)) h3⟩

/-- Any configuration of actual points is acyclic: take a hull edge. -/
lemma acyc_witness (A : Fin 5 → Pt)
    (hcoll : ∀ i j k : Fin 5, i ≠ j → j ≠ k → i ≠ k → darea (A i) (A j) (A k) ≠ 0) :
    acycB (sgn A) := by
  obtain ⟨i₀, hi₀, hmax⟩ :=
    Finset.exists_max_image Finset.univ (fun i => (A i) 0) Finset.univ_nonempty
  by_cases hu : ∃ j : Fin 5, j ≠ i₀ ∧ (A j) 0 = (A i₀) 0
  · -- two points share the maximal `x`-coordinate: their vertical line is a hull edge
    obtain ⟨j₀, hj₀, hjx⟩ := hu
    have hlt : ∀ k : Fin 5, k ≠ i₀ → k ≠ j₀ → (A k) 0 < (A i₀) 0 := by
      intro k hk1 hk2
      have hle := hmax k (Finset.mem_univ k)
      rcases lt_or_eq_of_le hle with h | h
      · exact h
      · exfalso
        have h0 : darea (A k) (A i₀) (A j₀) = 0 := by
          simp only [darea, cross, PiLp.sub_apply, h, hjx]
          ring
        exact hcoll k i₀ j₀ hk1 (Ne.symm hj₀) hk2 h0
    have hy : (A i₀) 1 ≠ (A j₀) 1 := by
      intro h
      have hpt : A i₀ = A j₀ := Pt_ext (fun i => by fin_cases i <;> simp [hjx, h])
      obtain ⟨k, hk1, hk2⟩ : ∃ k : Fin 5, k ≠ i₀ ∧ k ≠ j₀ := by
        have h1 : (Finset.univ \ {i₀, j₀} : Finset (Fin 5)).Nonempty := by
          rw [← Finset.card_pos]
          have h2 : ({i₀, j₀} : Finset (Fin 5)).card = 2 := by
            rw [Finset.card_insert_of_notMem (by simp [hj₀.symm]), Finset.card_singleton]
          rw [Finset.card_sdiff, Finset.card_univ, Fintype.card_fin, Finset.inter_univ, h2]
          decide
        obtain ⟨k, hk⟩ := h1
        simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or,
          Finset.mem_univ, true_and] at hk
        exact ⟨k, hk.1, hk.2⟩
      have h0 : darea (A k) (A i₀) (A j₀) = 0 := by
        rw [hpt]
        simp only [darea, cross, PiLp.sub_apply]
        ring
      exact hcoll k i₀ j₀ hk1 (Ne.symm hj₀) hk2 h0
    by_cases hσ : (A j₀) 1 < (A i₀) 1
    · refine ⟨j₀, i₀, hj₀, fun k hk1 hk2 => ?_⟩
      have hdk : 0 < darea (A j₀) (A i₀) (A k) := by
        have h1 : darea (A j₀) (A i₀) (A k) =
            ((A i₀) 0 - (A j₀) 0) * ((A k) 1 - (A j₀) 1) -
            ((A i₀) 1 - (A j₀) 1) * ((A k) 0 - (A j₀) 0) := by
          simp only [darea, cross, PiLp.sub_apply]
        have hk0 : (A k) 0 - (A i₀) 0 < 0 := by linarith [hlt k hk2 hk1]
        have hσ' : 0 < (A i₀) 1 - (A j₀) 1 := by linarith [hσ]
        have h2 := mul_neg_of_pos_of_neg hσ' hk0
        rw [h1, hjx]
        nlinarith [h2]
      rw [bit_eq hcoll j₀ i₀ k hj₀ (Ne.symm hk2) (Ne.symm hk1)]
      exact decide_eq_true hdk
    · have hσ2 : (A i₀) 1 < (A j₀) 1 := by
        rcases lt_or_gt_of_ne hy with h | h
        · exact h
        · exact absurd h hσ
      refine ⟨i₀, j₀, Ne.symm hj₀, fun k hk1 hk2 => ?_⟩
      have hdk : 0 < darea (A i₀) (A j₀) (A k) := by
        have h1 : darea (A i₀) (A j₀) (A k) =
            ((A j₀) 0 - (A i₀) 0) * ((A k) 1 - (A i₀) 1) -
            ((A j₀) 1 - (A i₀) 1) * ((A k) 0 - (A i₀) 0) := by
          simp only [darea, cross, PiLp.sub_apply]
        have hk0 : (A k) 0 - (A i₀) 0 < 0 := by linarith [hlt k hk1 hk2]
        have hσ' : 0 < (A j₀) 1 - (A i₀) 1 := by linarith [hσ2]
        have h2 := mul_neg_of_pos_of_neg hσ' hk0
        rw [h1, hjx]
        nlinarith [h2]
      rw [bit_eq hcoll i₀ j₀ k (Ne.symm hj₀) (Ne.symm hk2) (Ne.symm hk1)]
      exact decide_eq_true hdk
  · -- unique point with maximal `x`-coordinate: the max-slope ray from it is a hull edge
    push Not at hu
    have hlt : ∀ j : Fin 5, j ≠ i₀ → (A j) 0 < (A i₀) 0 := by
      intro j hj
      have hle := hmax j (Finset.mem_univ j)
      rcases lt_or_eq_of_le hle with h | h
      · exact h
      · exact absurd h (hu j hj)
    have hneS : (Finset.univ \ {i₀} : Finset (Fin 5)).Nonempty := by
      rw [← Finset.card_pos]
      rw [Finset.card_sdiff, Finset.card_univ, Fintype.card_fin, Finset.inter_univ,
        Finset.card_singleton]
      decide
    obtain ⟨j, hjmem, hjmax⟩ := Finset.exists_max_image (Finset.univ \ {i₀})
      (fun j => ((A j) 1 - (A i₀) 1) / ((A j) 0 - (A i₀) 0)) hneS
    have hj : j ≠ i₀ := by
      simp only [Finset.mem_sdiff, Finset.mem_singleton, Finset.mem_univ, true_and] at hjmem
      exact hjmem
    have hdk : ∀ k : Fin 5, k ≠ i₀ → k ≠ j → darea (A i₀) (A j) (A k) < 0 := by
      intro k hki₀ hkj
      have hkmem : k ∈ (Finset.univ \ {i₀} : Finset (Fin 5)) := by
        simp only [Finset.mem_sdiff, Finset.mem_singleton, Finset.mem_univ, true_and]
        exact hki₀
      have hks := hjmax k hkmem
      have hdk0 : (A k) 0 - (A i₀) 0 < 0 := by linarith [hlt k hki₀]
      have hdj0 : (A j) 0 - (A i₀) 0 < 0 := by linarith [hlt j hj]
      have hle2 : ((A j) 0 - (A i₀) 0) * ((A k) 1 - (A i₀) 1) -
          ((A j) 1 - (A i₀) 1) * ((A k) 0 - (A i₀) 0) ≤ 0 := by
        have hd1 : (A k) 0 - (A i₀) 0 ≠ 0 := ne_of_lt hdk0
        have hd2 : (A j) 0 - (A i₀) 0 ≠ 0 := ne_of_lt hdj0
        have h4 : 0 < ((A k) 0 - (A i₀) 0) * ((A j) 0 - (A i₀) 0) :=
          mul_pos_of_neg_of_neg hdk0 hdj0
        have h5 := mul_le_mul_of_nonneg_right hks h4.le
        have h7 : ((A k) 1 - (A i₀) 1) / ((A k) 0 - (A i₀) 0) *
            (((A k) 0 - (A i₀) 0) * ((A j) 0 - (A i₀) 0)) =
            ((A k) 1 - (A i₀) 1) * ((A j) 0 - (A i₀) 0) := by
          field_simp [hd1]
        have h8 : ((A j) 1 - (A i₀) 1) / ((A j) 0 - (A i₀) 0) *
            (((A k) 0 - (A i₀) 0) * ((A j) 0 - (A i₀) 0)) =
            ((A j) 1 - (A i₀) 1) * ((A k) 0 - (A i₀) 0) := by
          field_simp [hd2]
        rw [h7, h8] at h5
        nlinarith [h5]
      have h2 : darea (A i₀) (A j) (A k) =
          ((A j) 0 - (A i₀) 0) * ((A k) 1 - (A i₀) 1) -
          ((A j) 1 - (A i₀) 1) * ((A k) 0 - (A i₀) 0) := by
        simp only [darea, cross, PiLp.sub_apply]
      have hne0 := hcoll i₀ j k (Ne.symm hj) (Ne.symm hkj) (Ne.symm hki₀)
      rw [h2] at hne0 ⊢
      rcases lt_or_eq_of_le hle2 with h3 | h3
      · exact h3
      · exact absurd h3 hne0
    refine ⟨j, i₀, hj, fun k hk1 hk2 => ?_⟩
    rw [bit_eq hcoll j i₀ k hj (Ne.symm hk2) (Ne.symm hk1)]
    exact decide_eq_true (by rw [darea_swap21]; linarith [hdk k hk2 hk1])

/-- The beq of two sign-decides is the decide of the product's positivity. -/
lemma decide_beq_eq_decide_mul_pos {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) :
    (decide (0 < x) == decide (0 < y)) = decide (0 < x * y) := by
  rcases lt_or_gt_of_ne hx with h1 | h1 <;> rcases lt_or_gt_of_ne hy with h2 | h2
  · have g1 : decide ((0 : ℝ) < x) = false := decide_eq_false (by linarith)
    have g2 : decide ((0 : ℝ) < y) = false := decide_eq_false (by linarith)
    have g3 : decide ((0 : ℝ) < x * y) = true := decide_eq_true (mul_pos_of_neg_of_neg h1 h2)
    rw [g1, g2, g3]
    rfl
  · have g1 : decide ((0 : ℝ) < x) = false := decide_eq_false (by linarith)
    have g2 : decide ((0 : ℝ) < y) = true := decide_eq_true h2
    have g3 : decide ((0 : ℝ) < x * y) = false :=
      decide_eq_false (by rw [not_lt]; exact le_of_lt (mul_neg_of_neg_of_pos h1 h2))
    rw [g1, g2, g3]
    rfl
  · have g1 : decide ((0 : ℝ) < x) = true := decide_eq_true h1
    have g2 : decide ((0 : ℝ) < y) = false := decide_eq_false (by linarith)
    have g3 : decide ((0 : ℝ) < x * y) = false :=
      decide_eq_false (by rw [not_lt]; exact le_of_lt (mul_neg_of_pos_of_neg h1 h2))
    rw [g1, g2, g3]
    rfl
  · have g1 : decide ((0 : ℝ) < x) = true := decide_eq_true h1
    have g2 : decide ((0 : ℝ) < y) = true := decide_eq_true h2
    have g3 : decide ((0 : ℝ) < x * y) = true := decide_eq_true (mul_pos h1 h2)
    rw [g1, g2, g3]
    rfl

/-- If `t₁ + t₃ = t₂` and `t₁, t₃` have the same sign, then `t₂` shares it. -/
lemma relR_of_sum {t1 t2 t3 : ℝ} (h : t1 + t3 = t2) (hs : 0 < t1 ↔ 0 < t3) :
    (0 < t1 ↔ 0 < t2) := by
  constructor
  · intro h1
    have h3 : 0 < t3 := hs.mp h1
    linarith
  · intro h2
    by_contra h1
    have ht1 : t1 ≤ 0 := le_of_not_gt h1
    have ht3 : t3 ≤ 0 := by
      by_cases h3 : t3 ≤ 0
      · exact h3
      · push Not at h3
        exact absurd (hs.mpr h3) h1
    rcases lt_or_eq_of_le ht1 with h1' | h1'
    · linarith
    · rcases lt_or_eq_of_le ht3 with h3' | h3'
      · linarith
      · rw [h1', h3'] at h
        linarith

lemma classification {A : Fin 5 → Pt} {q : Fin 5 → ℝ}
    (hcoll : ∀ i j k : Fin 5, i ≠ j → j ≠ k → i ≠ k → darea (A i) (A j) (A k) ≠ 0)
    (harea : ∀ i j k : Fin 5, i ≠ j → j ≠ k → i ≠ k →
      |darea (A i) (A j) (A k)| = q i + q j + q k) :
    ∃ i j : Fin 5, i ≠ j ∧ q i = q j := by
  have n012 := hcoll 0 1 2 (by decide) (by decide) (by decide)
  have n013 := hcoll 0 1 3 (by decide) (by decide) (by decide)
  have n014 := hcoll 0 1 4 (by decide) (by decide) (by decide)
  have n023 := hcoll 0 2 3 (by decide) (by decide) (by decide)
  have n024 := hcoll 0 2 4 (by decide) (by decide) (by decide)
  have n034 := hcoll 0 3 4 (by decide) (by decide) (by decide)
  have n123 := hcoll 1 2 3 (by decide) (by decide) (by decide)
  have n124 := hcoll 1 2 4 (by decide) (by decide) (by decide)
  have n134 := hcoll 1 3 4 (by decide) (by decide) (by decide)
  have n234 := hcoll 2 3 4 (by decide) (by decide) (by decide)
  -- the Plücker sign constraints hold for the actual configuration
  have hpl : pluckerB (sgn A) := by
    refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩ <;> intro hs
    · rw [bit_eq hcoll 0 1 2 (by decide) (by decide) (by decide),
        bit_eq hcoll 0 3 4 (by decide) (by decide) (by decide)] at hs ⊢
      rw [bit_eq hcoll 0 1 4 (by decide) (by decide) (by decide),
        bit_eq hcoll 0 2 3 (by decide) (by decide) (by decide)] at hs
      rw [bit_eq hcoll 0 1 3 (by decide) (by decide) (by decide),
        bit_eq hcoll 0 2 4 (by decide) (by decide) (by decide)]
      rw [decide_beq_eq_decide_mul_pos n012 n034] at hs ⊢
      rw [decide_beq_eq_decide_mul_pos n014 n023] at hs
      rw [decide_beq_eq_decide_mul_pos n013 n024]
      have hsum := plucker0 A
      exact decide_eq_decide.mpr (relR_of_sum (by linarith [hsum]) (decide_eq_decide.mp hs))
    · rw [bit_eq hcoll 0 1 2 (by decide) (by decide) (by decide),
        bit_eq hcoll 1 3 4 (by decide) (by decide) (by decide)] at hs ⊢
      rw [bit_eq hcoll 0 1 4 (by decide) (by decide) (by decide),
        bit_eq hcoll 1 2 3 (by decide) (by decide) (by decide)] at hs
      rw [bit_eq hcoll 0 1 3 (by decide) (by decide) (by decide),
        bit_eq hcoll 1 2 4 (by decide) (by decide) (by decide)]
      rw [decide_beq_eq_decide_mul_pos n012 n134] at hs ⊢
      rw [decide_beq_eq_decide_mul_pos n014 n123] at hs
      rw [decide_beq_eq_decide_mul_pos n013 n124]
      have hsum := plucker1 A
      exact decide_eq_decide.mpr (relR_of_sum (by linarith [hsum]) (decide_eq_decide.mp hs))
    · rw [bit_eq hcoll 0 1 2 (by decide) (by decide) (by decide),
        bit_eq hcoll 2 3 4 (by decide) (by decide) (by decide)] at hs ⊢
      rw [bit_eq hcoll 0 2 4 (by decide) (by decide) (by decide),
        bit_eq hcoll 1 2 3 (by decide) (by decide) (by decide)] at hs
      rw [bit_eq hcoll 0 2 3 (by decide) (by decide) (by decide),
        bit_eq hcoll 1 2 4 (by decide) (by decide) (by decide)]
      rw [decide_beq_eq_decide_mul_pos n012 n234] at hs ⊢
      rw [decide_beq_eq_decide_mul_pos n024 n123] at hs
      rw [decide_beq_eq_decide_mul_pos n023 n124]
      have hsum := plucker2 A
      exact decide_eq_decide.mpr (relR_of_sum (by linarith [hsum]) (decide_eq_decide.mp hs))
    · rw [bit_eq hcoll 0 1 3 (by decide) (by decide) (by decide),
        bit_eq hcoll 2 3 4 (by decide) (by decide) (by decide)] at hs ⊢
      rw [bit_eq hcoll 0 3 4 (by decide) (by decide) (by decide),
        bit_eq hcoll 1 2 3 (by decide) (by decide) (by decide)] at hs
      rw [bit_eq hcoll 0 2 3 (by decide) (by decide) (by decide),
        bit_eq hcoll 1 3 4 (by decide) (by decide) (by decide)]
      rw [decide_beq_eq_decide_mul_pos n013 n234] at hs ⊢
      rw [decide_beq_eq_decide_mul_pos n034 n123] at hs
      rw [decide_beq_eq_decide_mul_pos n023 n134]
      have hsum := plucker3 A
      exact decide_eq_decide.mpr (relR_of_sum (by linarith [hsum]) (decide_eq_decide.mp hs))
    · rw [bit_eq hcoll 0 1 4 (by decide) (by decide) (by decide),
        bit_eq hcoll 2 3 4 (by decide) (by decide) (by decide)] at hs ⊢
      rw [bit_eq hcoll 0 3 4 (by decide) (by decide) (by decide),
        bit_eq hcoll 1 2 4 (by decide) (by decide) (by decide)] at hs
      rw [bit_eq hcoll 0 2 4 (by decide) (by decide) (by decide),
        bit_eq hcoll 1 3 4 (by decide) (by decide) (by decide)]
      rw [decide_beq_eq_decide_mul_pos n014 n234] at hs ⊢
      rw [decide_beq_eq_decide_mul_pos n034 n124] at hs
      rw [decide_beq_eq_decide_mul_pos n024 n134]
      have hsum := plucker4 A
      exact decide_eq_decide.mpr (relR_of_sum (by linarith [hsum]) (decide_eq_decide.mp hs))
  -- acyclicity holds for the actual configuration
  have hac : acycBB (sgn A) = true := (acycBB_iff _).mpr (acyc_witness A hcoll)
  -- run the finite check
  have hfin := sign_classify (sgn A) ((pluckerBB_iff _).mpr hpl) hac
  rcases hfin with h1 | h2 | h3
  · obtain ⟨a, b, c, d, e, ⟨⟨hab, hac, had, hae, hbc, hbd, hbe, hcd, hce, hde⟩, hq1⟩, hq2⟩ :=
      (C1B_iff _).mp h1
    have hQ1 := quadB_to_ConvQuad hcoll hab hac had hbc hbd hcd hq1
    have hQ2 := quadB_to_ConvQuad hcoll hab hac hae hbc hbe hce hq2
    have r1 := ConvQuad_rel hcoll harea hab hac had hbc hbd hcd hQ1
    have r2 := ConvQuad_rel hcoll harea hab hac hae hbc hbe hce hQ2
    exact ⟨d, e, hde, by linarith [r1, r2]⟩
  · obtain ⟨a, b, c, d, e, ⟨⟨hab, hac, had, hae, hbc, hbd, hbe, hcd, hce, hde⟩, hq1⟩, hq2⟩ :=
      (C2B_iff _).mp h2
    have hI1 := insideB_to_Inside hcoll (Ne.symm had) (Ne.symm hbd) (Ne.symm hcd) hab hac hbc hq1
    have hI2 := insideB_to_Inside hcoll (Ne.symm hae) (Ne.symm hbe) (Ne.symm hce) hab hac hbc hq2
    have r1 := Inside_rel hcoll harea (Ne.symm had) (Ne.symm hbd) (Ne.symm hcd) hab hac hbc hI1
    have r2 := Inside_rel hcoll harea (Ne.symm hae) (Ne.symm hbe) (Ne.symm hce) hab hac hbc hI2
    exact ⟨d, e, hde, by linarith [r1, r2]⟩
  · obtain ⟨a, b, c, d, e, ⟨⟨hab, hac, had, hae, hbc, hbd, hbe, hcd, hce, hde⟩, hq1⟩, hq2⟩ :=
      (C3B_iff _).mp h3
    have hQ1 := quadB_to_ConvQuad hcoll hab hac had hbc hbd hcd hq1
    have hQ2 := quadB_to_ConvQuad hcoll hab hae had hbe hbd (Ne.symm hde) hq2
    have r1 := ConvQuad_rel hcoll harea hab hac had hbc hbd hcd hQ1
    have r2 := ConvQuad_rel hcoll harea hab hae had hbe hbd (Ne.symm hde) hQ2
    exact ⟨c, e, hce, by linarith [r1, r2]⟩

/-- The case `n = 5` is impossible. -/
theorem not_config_five : ¬ Config 5 := by
  rintro ⟨A, r, hcoll, harea2⟩
  have harea : ∀ i j k : Fin 5, i ≠ j → j ≠ k → i ≠ k →
      |darea (A i) (A j) (A k)| = 2 * r i + 2 * r j + 2 * r k := by
    intro i j k hij hjk hik
    have h := harea2 i j k hij hjk hik
    have hpos : 0 ≤ |darea (A i) (A j) (A k)| := abs_nonneg _
    linarith [h]
  obtain ⟨i, j, hij, heq⟩ := classification (q := fun i => 2 * r i) hcoll harea
  exact q_ne_of_ne hcoll harea hij heq

/-- The case `n = 4` is realized by the four vertices of a square with all
`r i = 1/6`: every triangle has area `1/2`. -/
lemma config_four : Config 4 := by
  refine ⟨![!₂[(0:ℝ), (0:ℝ)], !₂[(1:ℝ), (0:ℝ)], !₂[(1:ℝ), (1:ℝ)], !₂[(0:ℝ), (1:ℝ)]],
    fun _ => 1/6, ?_, ?_⟩
  · intro i j k hij hjk hik
    fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all [darea, cross]
  · intro i j k hij hjk hik
    fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all [darea, cross] <;> norm_num
lemma config_restrict {n : ℕ} (h : Config n) (hn : 5 ≤ n) : Config 5 := by
  obtain ⟨A, r, hcoll, harea⟩ := h
  refine ⟨fun i => A (Fin.castLE hn i), fun i => r (Fin.castLE hn i), ?_, ?_⟩
  · intro i j k hij hjk hik
    exact hcoll _ _ _ ((Fin.castLE_injective hn).ne hij) ((Fin.castLE_injective hn).ne hjk)
      ((Fin.castLE_injective hn).ne hik)
  · intro i j k hij hjk hik
    exact harea _ _ _ ((Fin.castLE_injective hn).ne hij) ((Fin.castLE_injective hn).ne hjk)
      ((Fin.castLE_injective hn).ne hik)

snip end

problem imo1995_p3 : {n : ℕ | 3 < n ∧ Config n} = solution_set := by
  ext n
  simp only [Set.mem_setOf_eq, solution_set, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hn, hcfg⟩
    by_cases h4 : n = 4
    · exact h4
    · exfalso
      have h5 : 5 ≤ n := by omega
      exact not_config_five (config_restrict hcfg h5)
  · intro h
    subst h
    exact ⟨by norm_num, config_four⟩

end Imo1995P3
