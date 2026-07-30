/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Tactic
public import Mathlib.Analysis.Real.Sqrt
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Olympiad 1981, Problem 1

`P` is a point inside the triangle `ABC`. `D`, `E`, `F` are the feet of the
perpendiculars from `P` to the lines `BC`, `CA`, `AB` respectively. Find all
`P` which minimise `BC/PD + CA/PE + AB/PF`.

# Formal statement

The plane is coordinatized as `Point := Fin 2 → ℝ`. The triangle is given by
three points `A`, `B`, `C` with `cr (B - A) (C - A) ≠ 0` (non-collinear), and
a point `P` is inside the triangle if it is a barycentric combination of the
vertices with strictly positive coefficients. Since `D`, `E`, `F` are the
feet of the perpendiculars from `P`, the lengths `PD`, `PE`, `PF` are the
distances from `P` to the lines `BC`, `CA`, `AB`, which are computed with the
scalar cross product. We show that `P` minimises `BC/PD + CA/PE + AB/PF` if
and only if `P` is the incenter of the triangle, given by the standard
formula `(a • A + b • B + c • C) / (a + b + c)` where `a = BC`, `b = CA`,
`c = AB`.

# Solution

Follows https://prase.cz/kalva/imo/isoln/isoln811.html . If `P` has
barycentric coordinates `(α, β, γ)`, then `PD = α * 2 * area / BC`, etc.,
because `area PBC = α * area ABC`. Hence the objective equals
`(a²/α + b²/β + c²/γ) / (2 * area)`, and the Engel form of Cauchy–Schwarz
(Titu's lemma) gives `a²/α + b²/β + c²/γ ≥ (a + b + c)² / (α + β + γ)
= (a + b + c)²`, with equality if and only if `α : β : γ = a : b : c`, i.e.
if and only if `P` is the incenter.
-/

namespace Imo1981P1

/-- The Euclidean plane, coordinatized as `ℝ²`. -/
abbrev Point := Fin 2 → ℝ

/-- The Euclidean distance between two points of the plane. -/
noncomputable def Dist (A B : Point) : ℝ := Real.sqrt ((B 0 - A 0) ^ 2 + (B 1 - A 1) ^ 2)

/-- The scalar cross product (determinant) of two plane vectors; twice the
signed area of the triangle they span. -/
def cr (u v : Point) : ℝ := u 0 * v 1 - u 1 * v 0

/-- The distance from `P` to the line through `X` and `Y`. -/
noncomputable def distLine (P X Y : Point) : ℝ := |cr (P - X) (Y - X)| / Dist X Y

/-- `P` lies strictly inside the triangle `ABC`: it is a barycentric
combination of the vertices with strictly positive coefficients. -/
def Inside (A B C P : Point) : Prop :=
  ∃ α β γ : ℝ, 0 < α ∧ 0 < β ∧ 0 < γ ∧ α + β + γ = 1 ∧ P = α • A + β • B + γ • C

/-- The quantity to be minimized, `BC/PD + CA/PE + AB/PF`. -/
noncomputable def Obj (A B C P : Point) : ℝ :=
  Dist B C / distLine P B C + Dist C A / distLine P C A + Dist A B / distLine P A B

/-- The incenter of the triangle `ABC`, given by the standard formula
`(a • A + b • B + c • C) / (a + b + c)` with `a = BC`, `b = CA`, `c = AB`. -/
noncomputable def incenterPt (A B C : Point) : Point :=
  (Dist B C + Dist C A + Dist A B)⁻¹ •
    (Dist B C • A + Dist C A • B + Dist A B • C)

snip begin

/-- The key sum-of-squares identity underlying Titu's lemma:
`Σ a²βγ - (a+b+c)² αβγ = Σ (aβ - bα)² γ` when `α + β + γ = 1`. -/
lemma titu_id (a b c α β γ : ℝ) (hsum : α + β + γ = 1) :
    a ^ 2 * β * γ + b ^ 2 * α * γ + c ^ 2 * α * β - (a + b + c) ^ 2 * (α * β * γ) =
      (a * β - b * α) ^ 2 * γ + (b * γ - c * β) ^ 2 * α + (a * γ - c * α) ^ 2 * β := by
  have key : a ^ 2 * β * γ + b ^ 2 * α * γ + c ^ 2 * α * β - (a + b + c) ^ 2 * (α * β * γ) =
      (a * β - b * α) ^ 2 * γ + (b * γ - c * β) ^ 2 * α + (a * γ - c * α) ^ 2 * β +
      (1 - (α + β + γ)) * (a ^ 2 * β * γ + b ^ 2 * α * γ + c ^ 2 * α * β) := by
    ring
  rw [hsum] at key
  simpa using key

/-- Titu's lemma (Engel form of Cauchy–Schwarz) with three terms. -/
lemma titu_lb (a b c α β γ : ℝ) (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (hsum : α + β + γ = 1) :
    (a + b + c) ^ 2 ≤ a ^ 2 / α + b ^ 2 / β + c ^ 2 / γ := by
  have hpos : 0 < α * β * γ := mul_pos (mul_pos hα hβ) hγ
  have nα : α ≠ 0 := hα.ne'
  have nβ : β ≠ 0 := hβ.ne'
  have nγ : γ ≠ 0 := hγ.ne'
  have hfrac : a ^ 2 / α + b ^ 2 / β + c ^ 2 / γ =
      (a ^ 2 * β * γ + b ^ 2 * α * γ + c ^ 2 * α * β) / (α * β * γ) := by
    field_simp
  rw [hfrac, le_div_iff₀ hpos]
  have hM : 0 ≤ (a * β - b * α) ^ 2 * γ + (b * γ - c * β) ^ 2 * α +
      (a * γ - c * α) ^ 2 * β :=
    add_nonneg (add_nonneg (mul_nonneg (sq_nonneg _) hγ.le)
      (mul_nonneg (sq_nonneg _) hα.le)) (mul_nonneg (sq_nonneg _) hβ.le)
  have hid := titu_id a b c α β γ hsum
  linarith [hid, hM]

/-- The equality case of Titu's lemma. -/
lemma titu_eq (a b c α β γ : ℝ) (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (hsum : α + β + γ = 1) :
    a ^ 2 / α + b ^ 2 / β + c ^ 2 / γ = (a + b + c) ^ 2 ↔
      a * β = b * α ∧ b * γ = c * β ∧ a * γ = c * α := by
  have hpos : 0 < α * β * γ := mul_pos (mul_pos hα hβ) hγ
  have nα : α ≠ 0 := hα.ne'
  have nβ : β ≠ 0 := hβ.ne'
  have nγ : γ ≠ 0 := hγ.ne'
  have hfrac : a ^ 2 / α + b ^ 2 / β + c ^ 2 / γ =
      (a ^ 2 * β * γ + b ^ 2 * α * γ + c ^ 2 * α * β) / (α * β * γ) := by
    field_simp
  rw [hfrac, div_eq_iff hpos.ne']
  have hid := titu_id a b c α β γ hsum
  constructor
  · intro h
    have hM0 : (a * β - b * α) ^ 2 * γ + (b * γ - c * β) ^ 2 * α +
        (a * γ - c * α) ^ 2 * β = 0 := by linarith [h, hid]
    have g1 : 0 ≤ (a * β - b * α) ^ 2 * γ := mul_nonneg (sq_nonneg _) hγ.le
    have g2 : 0 ≤ (b * γ - c * β) ^ 2 * α := mul_nonneg (sq_nonneg _) hα.le
    have g3 : 0 ≤ (a * γ - c * α) ^ 2 * β := mul_nonneg (sq_nonneg _) hβ.le
    have e1 : (a * β - b * α) ^ 2 * γ = 0 := by linarith [hM0, g1, g2, g3]
    have e2 : (b * γ - c * β) ^ 2 * α = 0 := by linarith [hM0, g1, g2, g3]
    have e3 : (a * γ - c * α) ^ 2 * β = 0 := by linarith [hM0, g1, g2, g3]
    refine ⟨?_, ?_, ?_⟩
    · rcases mul_eq_zero.mp e1 with h2 | h2
      · exact sub_eq_zero.mp (sq_eq_zero_iff.mp h2)
      · exact absurd h2 hγ.ne'
    · rcases mul_eq_zero.mp e2 with h2 | h2
      · exact sub_eq_zero.mp (sq_eq_zero_iff.mp h2)
      · exact absurd h2 hα.ne'
    · rcases mul_eq_zero.mp e3 with h2 | h2
      · exact sub_eq_zero.mp (sq_eq_zero_iff.mp h2)
      · exact absurd h2 hβ.ne'
  · rintro ⟨h1, h2, h3⟩
    have hM0 : (a * β - b * α) ^ 2 * γ + (b * γ - c * β) ^ 2 * α +
        (a * γ - c * α) ^ 2 * β = 0 := by
      rw [sub_eq_zero.mpr h1, sub_eq_zero.mpr h2, sub_eq_zero.mpr h3]
      simp
    linarith [hid, hM0]

/-- From the equality conditions `aβ = bα`, `bγ = cβ`, `aγ = cα` and
`α + β + γ = 1`, the barycentric coordinates are those of the incenter. -/
lemma coords_of_eq (a b c α β γ : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hsum : α + β + γ = 1)
    (h : a * β = b * α ∧ b * γ = c * β ∧ a * γ = c * α) :
    α = a / (a + b + c) ∧ β = b / (a + b + c) ∧ γ = c / (a + b + c) := by
  obtain ⟨e1, e2, e3⟩ := h
  have hs : 0 < a + b + c := by positivity
  have k1 : α * (a + b + c) = a := by
    have h2 : a * (α + β + γ) = a := by rw [hsum]; ring
    linarith [e1, e3, h2]
  have k2 : β * (a + b + c) = b := by
    have h2 : b * (α + β + γ) = b := by rw [hsum]; ring
    linarith [e1, e2, h2]
  have k3 : γ * (a + b + c) = c := by
    have h2 : c * (α + β + γ) = c := by rw [hsum]; ring
    linarith [e2, e3, h2]
  refine ⟨?_, ?_, ?_⟩
  · rw [eq_div_iff hs.ne']
    exact k1
  · rw [eq_div_iff hs.ne']
    exact k2
  · rw [eq_div_iff hs.ne']
    exact k3

/-- The cross product of a vector with itself vanishes. -/
lemma cr_self (u : Point) : cr u u = 0 := by
  simp only [cr]
  ring

/-- The cross product is additive in its first argument. -/
lemma cr_add (u v w : Point) : cr (u + v) w = cr u w + cr v w := by
  simp only [cr, Pi.add_apply]
  ring

/-- The cross product is homogeneous in its first argument. -/
lemma cr_smul (r : ℝ) (u v : Point) : cr (r • u) v = r * cr u v := by
  simp only [cr, Pi.smul_apply, smul_eq_mul]
  ring

/-- The cross product with a zero left argument vanishes. -/
lemma cr_zero_left (v : Point) : cr 0 v = 0 := by
  simp only [cr, Pi.zero_apply]
  ring

/-- The cross product with a zero right argument vanishes. -/
lemma cr_zero_right (u : Point) : cr u 0 = 0 := by
  simp only [cr, Pi.zero_apply]
  ring

/-- Recentering a cross product at `B`. -/
lemma cr_A_sub_B (A B C : Point) : cr (A - B) (C - B) = -cr (B - A) (C - A) := by
  simp only [cr, Pi.sub_apply]
  ring

/-- Recentering a cross product at `C`. -/
lemma cr_B_sub_C (A B C : Point) : cr (B - C) (A - C) = -cr (B - A) (C - A) := by
  simp only [cr, Pi.sub_apply]
  ring

/-- Swapping the arguments of a cross product negates it. -/
lemma cr_C_sub_A (A B C : Point) : cr (C - A) (B - A) = -cr (B - A) (C - A) := by
  simp only [cr, Pi.sub_apply]
  ring

/-- Componentwise formula for a barycentric combination. -/
lemma bary_apply (A B C P : Point) (α β γ : ℝ) (hP : P = α • A + β • B + γ • C)
    (i : Fin 2) : P i = α * A i + β * B i + γ * C i := by
  rw [hP]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]

/-- `P - B` in terms of the barycentric coordinates of `P`. -/
lemma bary_sub_B (A B C P : Point) (α β γ : ℝ) (hsum : α + β + γ = 1)
    (hP : P = α • A + β • B + γ • C) : P - B = α • (A - B) + γ • (C - B) := by
  funext i
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    bary_apply A B C P α β γ hP i]
  have hs : (α + β + γ) * B i = B i := by rw [hsum]; ring
  linarith [hs]

/-- `P - C` in terms of the barycentric coordinates of `P`. -/
lemma bary_sub_C (A B C P : Point) (α β γ : ℝ) (hsum : α + β + γ = 1)
    (hP : P = α • A + β • B + γ • C) : P - C = α • (A - C) + β • (B - C) := by
  funext i
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    bary_apply A B C P α β γ hP i]
  have hs : (α + β + γ) * C i = C i := by rw [hsum]; ring
  linarith [hs]

/-- `P - A` in terms of the barycentric coordinates of `P`. -/
lemma bary_sub_A (A B C P : Point) (α β γ : ℝ) (hsum : α + β + γ = 1)
    (hP : P = α • A + β • B + γ • C) : P - A = β • (B - A) + γ • (C - A) := by
  funext i
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    bary_apply A B C P α β γ hP i]
  have hs : (α + β + γ) * A i = A i := by rw [hsum]; ring
  linarith [hs]

/-- The cross product giving twice the signed area of `PBC`, in terms of the
barycentric coordinate `α` of `P`. -/
lemma distLine_BC_eq (A B C P : Point) (α β γ : ℝ) (hα : 0 ≤ α)
    (hsum : α + β + γ = 1) (hP : P = α • A + β • B + γ • C) :
    |cr (P - B) (C - B)| = α * |cr (B - A) (C - A)| := by
  rw [bary_sub_B A B C P α β γ hsum hP]
  simp only [cr_add, cr_smul, cr_self, mul_zero, add_zero]
  rw [cr_A_sub_B, abs_mul, abs_neg, abs_of_nonneg hα]

/-- The cross product giving twice the signed area of `PCA`, in terms of the
barycentric coordinate `β` of `P`. -/
lemma distLine_CA_eq (A B C P : Point) (α β γ : ℝ) (hβ : 0 ≤ β)
    (hsum : α + β + γ = 1) (hP : P = α • A + β • B + γ • C) :
    |cr (P - C) (A - C)| = β * |cr (B - A) (C - A)| := by
  rw [bary_sub_C A B C P α β γ hsum hP]
  simp only [cr_add, cr_smul, cr_self, mul_zero, zero_add]
  rw [cr_B_sub_C, abs_mul, abs_neg, abs_of_nonneg hβ]

/-- The cross product giving twice the signed area of `PAB`, in terms of the
barycentric coordinate `γ` of `P`. -/
lemma distLine_AB_eq (A B C P : Point) (α β γ : ℝ) (hγ : 0 ≤ γ)
    (hsum : α + β + γ = 1) (hP : P = α • A + β • B + γ • C) :
    |cr (P - A) (B - A)| = γ * |cr (B - A) (C - A)| := by
  rw [bary_sub_A A B C P α β γ hsum hP]
  simp only [cr_add, cr_smul, cr_self, mul_zero, zero_add]
  rw [cr_C_sub_A, abs_mul, abs_neg, abs_of_nonneg hγ]

/-- The distance between two distinct points is positive. -/
lemma dist_pos_of_ne {X Y : Point} (h : X ≠ Y) : 0 < Dist X Y := by
  have hne : Y 0 - X 0 ≠ 0 ∨ Y 1 - X 1 ≠ 0 := by
    by_contra hc
    push Not at hc
    obtain ⟨h0, h1⟩ := hc
    exact h (funext fun i => by
      fin_cases i <;> simp [sub_eq_zero.mp h0, sub_eq_zero.mp h1])
  simp only [Dist, Real.sqrt_pos]
  rcases hne with h0 | h1
  · have hp := sq_pos_of_ne_zero h0
    have hq := sq_nonneg (Y 1 - X 1)
    linarith [hp, hq]
  · have hp := sq_pos_of_ne_zero h1
    have hq := sq_nonneg (Y 0 - X 0)
    linarith [hp, hq]

/-- If the twice signed area of `ABC` is nonzero, the vertices are distinct. -/
lemma ne_of_cr_ne_zero {A B C : Point} (h : cr (B - A) (C - A) ≠ 0) :
    B ≠ C ∧ C ≠ A ∧ A ≠ B := by
  refine ⟨fun hBC => h ?_, fun hCA => h ?_, fun hAB => h ?_⟩
  · rw [hBC]
    exact cr_self _
  · rw [hCA, sub_self]
    exact cr_zero_right _
  · rw [hAB, sub_self]
    exact cr_zero_left _

/-- The objective function at an interior point, in terms of its barycentric
coordinates: `Obj = (a²/α + b²/β + c²/γ) / (2 * area)`. -/
lemma obj_eq (A B C P : Point) (α β γ : ℝ) (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (hsum : α + β + γ = 1) (hP : P = α • A + β • B + γ • C)
    (ha : 0 < Dist B C) (hb : 0 < Dist C A) (hc : 0 < Dist A B)
    (ht : 0 < |cr (B - A) (C - A)|) :
    Obj A B C P = ((Dist B C) ^ 2 / α + (Dist C A) ^ 2 / β + (Dist A B) ^ 2 / γ) /
      |cr (B - A) (C - A)| := by
  unfold Obj distLine
  rw [distLine_BC_eq A B C P α β γ hα.le hsum hP,
    distLine_CA_eq A B C P α β γ hβ.le hsum hP,
    distLine_AB_eq A B C P α β γ hγ.le hsum hP]
  have n1 : Dist B C ≠ 0 := ha.ne'
  have n2 : Dist C A ≠ 0 := hb.ne'
  have n3 : Dist A B ≠ 0 := hc.ne'
  have n4 : |cr (B - A) (C - A)| ≠ 0 := ht.ne'
  have n5 : α ≠ 0 := hα.ne'
  have n6 : β ≠ 0 := hβ.ne'
  have n7 : γ ≠ 0 := hγ.ne'
  field_simp

/-- The incenter as a barycentric combination with positive coefficients. -/
lemma incenterPt_eq (A B C : Point) :
    incenterPt A B C = (Dist B C / (Dist B C + Dist C A + Dist A B)) • A +
      (Dist C A / (Dist B C + Dist C A + Dist A B)) • B +
      (Dist A B / (Dist B C + Dist C A + Dist A B)) • C := by
  funext i
  simp only [incenterPt, Pi.add_apply, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv]
  ring

snip end

/-- The answer: the unique point minimizing `BC/PD + CA/PE + AB/PF` is the
incenter of the triangle. -/
noncomputable determine solution_point (A B C : Point) : Point := incenterPt A B C

problem imo1981_p1 (A B C : Point) (hABC : cr (B - A) (C - A) ≠ 0) (P : Point)
    (hP : Inside A B C P) :
    (∀ Q : Point, Inside A B C Q → Obj A B C P ≤ Obj A B C Q) ↔
      P = solution_point A B C := by
  obtain ⟨α, β, γ, hα, hβ, hγ, hsum, hPb⟩ := hP
  obtain ⟨hBC, hCA, hAB⟩ := ne_of_cr_ne_zero hABC
  have ha : 0 < Dist B C := dist_pos_of_ne hBC
  have hb : 0 < Dist C A := dist_pos_of_ne hCA
  have hc : 0 < Dist A B := dist_pos_of_ne hAB
  have ht : 0 < |cr (B - A) (C - A)| := abs_pos.mpr hABC
  have hs : 0 < Dist B C + Dist C A + Dist A B := by positivity
  -- The objective at any interior point, in barycentric coordinates.
  have obj_eq_of : ∀ (Q : Point) (α' β' γ' : ℝ), 0 < α' → 0 < β' → 0 < γ' →
      α' + β' + γ' = 1 → Q = α' • A + β' • B + γ' • C →
      Obj A B C Q = ((Dist B C) ^ 2 / α' + (Dist C A) ^ 2 / β' + (Dist A B) ^ 2 / γ') /
        |cr (B - A) (C - A)| :=
    fun Q α' β' γ' hα' hβ' hγ' hsum' hQ =>
      obj_eq A B C Q α' β' γ' hα' hβ' hγ' hsum' hQ ha hb hc ht
  -- The incenter is strictly inside the triangle.
  have hI0 : incenterPt A B C = (Dist B C / (Dist B C + Dist C A + Dist A B)) • A +
      (Dist C A / (Dist B C + Dist C A + Dist A B)) • B +
      (Dist A B / (Dist B C + Dist C A + Dist A B)) • C := incenterPt_eq A B C
  have hIsum : Dist B C / (Dist B C + Dist C A + Dist A B) +
      Dist C A / (Dist B C + Dist C A + Dist A B) +
      Dist A B / (Dist B C + Dist C A + Dist A B) = 1 := by
    have ns : Dist B C + Dist C A + Dist A B ≠ 0 := hs.ne'
    field_simp
  have hIin : Inside A B C (incenterPt A B C) :=
    ⟨Dist B C / (Dist B C + Dist C A + Dist A B),
      Dist C A / (Dist B C + Dist C A + Dist A B),
      Dist A B / (Dist B C + Dist C A + Dist A B),
      div_pos ha hs, div_pos hb hs, div_pos hc hs, hIsum, hI0⟩
  -- The objective at the incenter equals the lower bound `(a + b + c)²/(2·area)`.
  have hObjI : Obj A B C (incenterPt A B C) =
      (Dist B C + Dist C A + Dist A B) ^ 2 / |cr (B - A) (C - A)| := by
    rw [obj_eq_of _ _ _ _ (div_pos ha hs) (div_pos hb hs) (div_pos hc hs) hIsum hI0]
    have n1 : Dist B C ≠ 0 := ha.ne'
    have n2 : Dist C A ≠ 0 := hb.ne'
    have n3 : Dist A B ≠ 0 := hc.ne'
    have n4 : |cr (B - A) (C - A)| ≠ 0 := ht.ne'
    have ns : Dist B C + Dist C A + Dist A B ≠ 0 := hs.ne'
    field_simp
  constructor
  · -- A minimizer must be the incenter.
    intro hmin
    have h1 : Obj A B C P ≤ Obj A B C (incenterPt A B C) := hmin _ hIin
    rw [hObjI] at h1
    have hbnd : (Dist B C + Dist C A + Dist A B) ^ 2 / |cr (B - A) (C - A)| ≤
        Obj A B C P := by
      rw [obj_eq_of P α β γ hα hβ hγ hsum hPb]
      rw [div_le_div_iff_of_pos_right ht]
      exact titu_lb _ _ _ _ _ _ hα hβ hγ hsum
    have heq : Obj A B C P = (Dist B C + Dist C A + Dist A B) ^ 2 /
        |cr (B - A) (C - A)| := le_antisymm h1 hbnd
    rw [obj_eq_of P α β γ hα hβ hγ hsum hPb] at heq
    have hsum2 : (Dist B C) ^ 2 / α + (Dist C A) ^ 2 / β + (Dist A B) ^ 2 / γ =
        (Dist B C + Dist C A + Dist A B) ^ 2 :=
      mul_right_cancel₀ (inv_ne_zero ht.ne') heq
    have hconds := (titu_eq _ _ _ _ _ _ hα hβ hγ hsum).mp hsum2
    obtain ⟨r1, r2, r3⟩ := coords_of_eq _ _ _ _ _ _ ha hb hc hsum hconds
    show P = incenterPt A B C
    rw [hPb, r1, r2, r3]
    exact hI0.symm
  · -- The incenter is a minimizer.
    intro hPeq Q hQ
    obtain ⟨α', β', γ', hα', hβ', hγ', hsum', hQb⟩ := hQ
    have hPeq' : P = incenterPt A B C := hPeq
    rw [hPeq', hObjI, obj_eq_of Q α' β' γ' hα' hβ' hγ' hsum' hQb,
      div_le_div_iff_of_pos_right ht]
    exact titu_lb _ _ _ _ _ _ hα' hβ' hγ' hsum'

end Imo1981P1
