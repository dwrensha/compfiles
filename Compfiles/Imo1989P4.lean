/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Euclidean.Projection
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity.Basic
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Olympiad 1989, Problem 4

Let $ABCD$ be a convex quadrilateral such that the sides $AB$, $AD$, $BC$
satisfy $AB = AD + BC$. There exists a point $P$ inside the quadrilateral
at a distance $h$ from the line $CD$ such that $AP = h + AD$ and
$BP = h + BC$. Show that:
$$ \frac{1}{\sqrt{h}} \geq \frac{1}{\sqrt{AD}} + \frac{1}{\sqrt{BC}}. $$

## Solution sketch (after Gerhard Wöginger)

Let $C_A$ be the circle with center $A$ and radius $AD$, and $C_B$ the circle
with center $B$ and radius $BC$; the two circles touch each other since
$AB = AD + BC$. The circle $C_P$ with center $P$ and radius $h$ touches $C_A$,
$C_B$ and the line $CD$. Let $t$ be the common tangent to $C_A$ and $C_B$
whose points of contact are on the same side of $AB$ as $C$ and $D$. Then
$C_P$ is confined inside the curvilinear triangle bounded by $t$, $C_A$ and
$C_B$, so $h$ is at most the value attained when $C_P$ also touches $t$. In
that extremal configuration the angles $\angle ADC$ and $\angle BCD$ are right
angles, so $CD^2 = AB^2 - (AD - BC)^2 = 4 \cdot AD \cdot BC$; similarly, if
$E$ is the point where $t$ touches $C_P$, then $DE^2 = 4h \cdot AD$ and
$CE^2 = 4h \cdot BC$. Since $CD = DE + CE$, we get
$1/\sqrt{h} = 1/\sqrt{AD} + 1/\sqrt{BC}$ in the extremal case, which gives
the inequality in general.

## Formalization note

We work in coordinates: put $a = AD$, $b = BC$, place $A = (0, 0)$ and
$B = (a + b, 0)$ (using $AB = AD + BC$) and take the side of $AB$ containing
$C$, $D$ (and hence $P$) to have positive second coordinate; `hpy` records
this orientation choice. The hypotheses `hAP`, `hBP`, `hAD`, `hBC` are the
side-length conditions $AP = h + a$, $BP = h + b$, $AD = a$, $BC = b$;
`hdist` says that the distance from `P` to the line `CD` (i.e. to its
orthogonal projection on `line[ℝ, C, D]`) equals `h`; `hP` says that `P`
lies in the interior of the convex hull of the four vertices, which is the
content of "`ABCD` is a convex quadrilateral and `P` is inside it" that the
proof uses.

The confinement step of the sketch — the circle around $P$ stays below the
common external tangent line $t$ — is *derived* in the lemma `confine`:
writing $P$ as a convex combination of the four vertices (from `hP`) and
evaluating the two affine functions $f(X) = \langle X, n_0 \rangle$ (height
towards $t$) and $g(X) = \langle X - Q, \hat m \rangle$ (signed distance to
the line $CD$, with $Q$ the foot of the perpendicular from $P$ and
$\hat m = (P-Q)/h$) on this combination gives
$\langle P, n_0 \rangle \le a - a w_A - b w_B$ and
$h \le a w_A + b w_B$, hence $\langle P, n_0 \rangle \le a - h$, i.e.
$\operatorname{dist}(P, t) \ge h$. The interior-hull hypothesis is essential:
the metric equations alone admit spurious configurations with arbitrarily
large $h$.

From here the proof is purely algebraic. The two distance equations give
$p_x = a + h(a-b)/(a+b)$ and $p_y^2 = 4abh(a+b+h)/(a+b)^2$; substituting in
the confinement inequality yields, with
$G(x) := x(a^2+b^2) + 2ab\sqrt{x(a+b+x)}$, that $G(h) \le ab(a+b)$.
But $G$ is strictly increasing on $(0, \infty)$ and a direct computation
shows $G(h_0) = ab(a+b)$ for $h_0 := ab/(\sqrt a + \sqrt b)^2$, so
$h \le h_0$, which rearranges to
$1/\sqrt{h} \ge 1/\sqrt{a} + 1/\sqrt{b}$.
-/

namespace Imo1989P4

open Affine EuclideanGeometry
open scoped Real RealInnerProductSpace

abbrev Pt := EuclideanSpace ℝ (Fin 2)

snip begin

/-- Distance in the plane in terms of coordinates. -/
lemma dist_eq (x y : Pt) : dist x y = √((x 0 - y 0)^2 + (x 1 - y 1)^2) := by
  rw [dist_eq_norm, EuclideanSpace.norm_eq, Fin.sum_univ_two]
  simp only [WithLp.ofLp_sub, Pi.sub_apply, Real.norm_eq_abs, sq_abs]

/-- The unit normal of the common external tangent line `t` of the circles
centered at `0` with radius `a` and centered at `(a+b, 0)` with radius `b`
(on the side of positive second coordinate): `t` is the line
`⟪X, commonTangentNormal a b⟫ = a`. -/
noncomputable def commonTangentNormal (a b : ℝ) : Pt :=
  !₂[(a - b) / (a + b), 2 * √(a * b) / (a + b)]

lemma commonTangentNormal_norm {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ‖commonTangentNormal a b‖ = 1 := by
  have habp : (0 : ℝ) < a + b := by positivity
  have hne : a + b ≠ 0 := ne_of_gt habp
  have e0 : (commonTangentNormal a b) 0 = (a - b) / (a + b) := by
    rw [commonTangentNormal]
    simp
  have e1 : (commonTangentNormal a b) 1 = 2 * √(a * b) / (a + b) := by
    rw [commonTangentNormal]
    simp
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, e0, e1, Real.norm_eq_abs, Real.norm_eq_abs,
    sq_abs, sq_abs]
  rw [show ((a - b) / (a + b))^2 + (2 * √(a * b) / (a + b))^2 = 1 by
    rw [div_pow, div_pow, mul_pow, Real.sq_sqrt (show (0 : ℝ) ≤ a * b by positivity)]
    field_simp
    ring]
  exact Real.sqrt_one

/-- Inner product with an explicitly given vector. -/
lemma inner_mk_right (z : Pt) (x y : ℝ) : ⟪z, (!₂[x, y] : Pt)⟫ = z 0 * x + z 1 * y := by
  have e0 : (!₂[x, y] : Pt) 0 = x := by simp
  have e1 : (!₂[x, y] : Pt) 1 = y := by simp
  rw [PiLp.inner_apply, Fin.sum_univ_two, e0, e1, RCLike.inner_apply, RCLike.inner_apply,
    RCLike.conj_to_real, RCLike.conj_to_real]
  ring

/-- Pythagoras: if `u` is a unit vector orthogonal to `y`, then the component
of `x` along `u` is bounded by `‖x - y‖`. This is the "distance to the line
through `y` perpendicular to `u` is at most `‖x - y‖`" step. -/
lemma sq_inner_le {u x y : Pt} (hu : ⟪u, u⟫ = 1) (hy : ⟪y, u⟫ = 0) :
    (⟪x, u⟫)^2 ≤ ‖x - y‖^2 := by
  have hdecomp : x - y = ⟪x, u⟫ • u + ((x - ⟪x, u⟫ • u) - y) := by abel
  have horth : ⟪⟪x, u⟫ • u, (x - ⟪x, u⟫ • u) - y⟫ = 0 := by
    rw [real_inner_smul_left, inner_sub_right, inner_sub_right, real_inner_smul_right, hu,
      real_inner_comm y u, hy, real_inner_comm x u]
    ring
  have hpyth := norm_add_sq_eq_norm_sq_add_norm_sq_real horth
  rw [← hdecomp] at hpyth
  have hu1 : ‖u‖ = 1 := by
    have h1 : ‖u‖^2 = 1 := by rw [← real_inner_self_eq_norm_sq, hu]
    have h2 : 0 ≤ ‖u‖ := norm_nonneg u
    rcases sq_eq_one_iff.mp h1 with h | h
    · exact h
    · linarith
  have e1 : ‖⟪x, u⟫ • u‖ = |⟪x, u⟫| := by
    rw [norm_smul, hu1, mul_one, Real.norm_eq_abs]
  rw [e1] at hpyth
  have e2 : (0 : ℝ) ≤ ‖(x - ⟪x, u⟫ • u) - y‖ * ‖(x - ⟪x, u⟫ • u) - y‖ := by positivity
  have e3 : |⟪x, u⟫| * |⟪x, u⟫| = (⟪x, u⟫)^2 := by
    rw [← sq_abs]
    ring
  have e4 : ‖x - y‖ * ‖x - y‖ = ‖x - y‖^2 := by ring
  rw [e3, e4] at hpyth
  linarith [hpyth, e2]

/-- **The confinement step** (the geometric heart of the problem).

The circle around `P` of radius `h` stays below the common external tangent
line `t` of the two circles: `⟪P, n₀⟫ ≤ a - h` where `n₀` is the unit normal
of `t`; multiplied through by `a + b` this is the displayed inequality.

Proof: write `P` as a convex combination `P = Σ wᵢ Vᵢ` of the four vertices
(possible since `P ∈ convexHull {A, B, C, D}`). For the affine function
`f(X) = ⟪X, n₀⟫` we have `f(A) = 0`, `f(B) = a - b`, `f(C), f(D) ≤ a`
(the circles are tangent to `t`), hence
`f(P) ≤ a - a·w_A - b·w_B`. For the affine function
`g(X) = ⟪X - Q, m̂⟫` (signed distance to the line `CD`, with `Q` the foot of
the perpendicular from `P` and `m̂ = (P - Q)/h`) we have `g(C) = g(D) = 0`,
`g(P) = h`, `g(A) ≤ a`, `g(B) ≤ b` (Pythagoras), hence
`h = g(P) = w_A·g(A) + w_B·g(B) ≤ a·w_A + b·w_B`. Combining the two
inequalities gives `f(P) ≤ a - h`. The convex-combination hypothesis is what
rules out the spurious large-`h` configurations that satisfy all the metric
equations but have `P` far outside the quadrilateral. -/
lemma confine {a b h : ℝ} (ha : 0 < a) (hb : 0 < b) (hh : 0 < h)
    (P C D : Pt)
    (hAD : dist D 0 = a) (hBC : dist C !₂[a + b, 0] = b)
    (hdist : dist P (orthogonalProjection line[ℝ, C, D] P : Pt) = h)
    (hP : P ∈ interior (convexHull ℝ (({0, !₂[a + b, 0], C, D} : Finset Pt) : Set Pt))) :
    (a - b) * P 0 + 2 * √(a * b) * P 1 ≤ (a - h) * (a + b) := by
  have habp : (0 : ℝ) < a + b := by positivity
  have hne : a + b ≠ 0 := ne_of_gt habp
  set Q : Pt := (orthogonalProjection line[ℝ, C, D] P : Pt) with hQdef
  -- f-values
  have f0 : ⟪(0 : Pt), commonTangentNormal a b⟫ = 0 := by simp
  have fB : ⟪(!₂[a + b, 0] : Pt), commonTangentNormal a b⟫ = a - b := by
    have e0 : (!₂[a + b, 0] : Pt) 0 = a + b := by simp
    have e1 : (!₂[a + b, 0] : Pt) 1 = (0 : ℝ) := by simp
    rw [commonTangentNormal, inner_mk_right, e0, e1]
    field_simp
    ring
  have fC : ⟪C, commonTangentNormal a b⟫ ≤ a := by
    have e1 : ⟪C, commonTangentNormal a b⟫
        = ⟪(!₂[a + b, 0] : Pt), commonTangentNormal a b⟫
          + ⟪C - !₂[a + b, 0], commonTangentNormal a b⟫ := by
      rw [← inner_add_left]
      congr 1
      abel
    have e2 : ⟪C - !₂[a + b, 0], commonTangentNormal a b⟫
        ≤ ‖C - !₂[a + b, 0]‖ * ‖commonTangentNormal a b‖ := real_inner_le_norm _ _
    have e3 : ‖C - !₂[a + b, 0]‖ = b := by
      rw [dist_eq_norm] at hBC
      exact hBC
    rw [fB] at e1
    rw [e3, commonTangentNormal_norm ha hb, mul_one] at e2
    linarith [e1, e2]
  have fD : ⟪D, commonTangentNormal a b⟫ ≤ a := by
    have e2 : ⟪D, commonTangentNormal a b⟫ ≤ ‖D‖ * ‖commonTangentNormal a b‖ :=
      real_inner_le_norm _ _
    have e3 : ‖D‖ = a := by
      rw [dist_eq_norm, sub_zero] at hAD
      exact hAD
    rw [e3, commonTangentNormal_norm ha hb, mul_one] at e2
    exact e2
  -- the foot Q and the signed distance g
  have hQmem : Q ∈ line[ℝ, C, D] := by
    rw [hQdef]
    exact orthogonalProjection_mem _
  have hCmem : C ∈ line[ℝ, C, D] := left_mem_affineSpan_pair ℝ C D
  have hDmem : D ∈ line[ℝ, C, D] := right_mem_affineSpan_pair ℝ C D
  have hmnorm : ‖P - Q‖ = h := by
    rw [dist_eq_norm] at hdist
    exact hdist
  have hhn : (h : ℝ) ≠ 0 := ne_of_gt hh
  have hmorth : (P - Q) ∈ (line[ℝ, C, D]).directionᗮ := by
    have h1 := vsub_orthogonalProjection_mem_direction_orthogonal line[ℝ, C, D] P
    rwa [vsub_eq_sub, ← hQdef] at h1
  have hCQ : (C - Q) ∈ (line[ℝ, C, D]).direction := by
    have h1 := AffineSubspace.vsub_mem_direction hCmem hQmem
    rwa [vsub_eq_sub] at h1
  have hDQ : (D - Q) ∈ (line[ℝ, C, D]).direction := by
    have h1 := AffineSubspace.vsub_mem_direction hDmem hQmem
    rwa [vsub_eq_sub] at h1
  have gC0 : ⟪C - Q, P - Q⟫ = 0 := Submodule.inner_right_of_mem_orthogonal hCQ hmorth
  have gD0 : ⟪D - Q, P - Q⟫ = 0 := Submodule.inner_right_of_mem_orthogonal hDQ hmorth
  have hu : ⟪h⁻¹ • (P - Q), h⁻¹ • (P - Q)⟫ = 1 := by
    rw [real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq, hmnorm]
    field_simp
  have gC : ⟪C - Q, h⁻¹ • (P - Q)⟫ = 0 := by
    rw [real_inner_smul_right, gC0, mul_zero]
  have gD : ⟪D - Q, h⁻¹ • (P - Q)⟫ = 0 := by
    rw [real_inner_smul_right, gD0, mul_zero]
  have gP : ⟪P - Q, h⁻¹ • (P - Q)⟫ = h := by
    rw [real_inner_smul_right, real_inner_self_eq_norm_sq, hmnorm]
    field_simp
  have g0sq : (⟪(0 : Pt) - Q, h⁻¹ • (P - Q)⟫)^2 ≤ a^2 := by
    have h1 := sq_inner_le hu gD (x := (0 : Pt) - Q)
    have h2 : ((0 : Pt) - Q) - (D - Q) = -D := by abel
    have h3 : ‖D‖ = a := by
      rw [dist_eq_norm, sub_zero] at hAD
      exact hAD
    rw [h2, norm_neg, h3] at h1
    exact h1
  have gBsq : (⟪!₂[a + b, 0] - Q, h⁻¹ • (P - Q)⟫)^2 ≤ b^2 := by
    have h1 := sq_inner_le hu gC (x := !₂[a + b, 0] - Q)
    have h2 : (!₂[a + b, 0] - Q) - (C - Q) = !₂[a + b, 0] - C := by abel
    have h3 : ‖C - !₂[a + b, 0]‖ = b := by
      rw [dist_eq_norm] at hBC
      exact hBC
    rw [h2, show (!₂[a + b, 0] : Pt) - C = -(C - !₂[a + b, 0]) by abel, norm_neg, h3] at h1
    exact h1
  have g0_le : ⟪(0 : Pt) - Q, h⁻¹ • (P - Q)⟫ ≤ a := by
    have h1 : |⟪(0 : Pt) - Q, h⁻¹ • (P - Q)⟫| ≤ a := by
      have h2 := sq_le_sq.mp g0sq
      rwa [abs_of_pos ha] at h2
    exact le_trans (le_abs_self _) h1
  have gB_le : ⟪!₂[a + b, 0] - Q, h⁻¹ • (P - Q)⟫ ≤ b := by
    have h1 : |⟪!₂[a + b, 0] - Q, h⁻¹ • (P - Q)⟫| ≤ b := by
      have h2 := sq_le_sq.mp gBsq
      rwa [abs_of_pos hb] at h2
    exact le_trans (le_abs_self _) h1
  -- the convex combination
  set s : Finset Pt := {0, !₂[a + b, 0], C, D} with hsdef
  have hPhull : P ∈ convexHull ℝ (s : Set Pt) := interior_subset hP
  rw [Finset.convexHull_eq] at hPhull
  obtain ⟨w, hw0, hw1, hcm⟩ := hPhull
  rw [Finset.centerMass_eq_of_sum_1 _ _ hw1] at hcm
  simp only [id_eq] at hcm
  have h0s : (0 : Pt) ∈ s := by
    rw [hsdef]
    exact Finset.mem_insert_self _ _
  have hBne0 : (!₂[a + b, 0] : Pt) ≠ 0 := by
    intro hcon
    have h1 : (!₂[a + b, 0] : Pt) 0 = (0 : Pt) 0 := by rw [hcon]
    simp at h1
    linarith
  have hBs : (!₂[a + b, 0] : Pt) ∈ s.erase 0 := by
    rw [Finset.mem_erase]
    refine ⟨hBne0, ?_⟩
    rw [hsdef]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hyCD : ∀ y ∈ (s.erase 0).erase !₂[a + b, 0], y = C ∨ y = D := by
    intro y hy
    have hyne0 : y ≠ (0 : Pt) := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hy)).1
    have hyneB : y ≠ !₂[a + b, 0] := (Finset.mem_erase.mp hy).1
    have hys : y ∈ s := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hy)
    rw [hsdef] at hys
    simp only [Finset.mem_insert, Finset.mem_singleton] at hys
    rcases hys with rfl | rfl | rfl | rfl
    · exact absurd rfl hyne0
    · exact absurd rfl hyneB
    · exact Or.inl rfl
    · exact Or.inr rfl
  have split_w : w 0 + w !₂[a + b, 0] + ∑ y ∈ (s.erase 0).erase !₂[a + b, 0], w y = 1 := by
    rw [← hw1, ← Finset.add_sum_erase s w h0s, ← Finset.add_sum_erase _ w hBs]
    ring
  have split_f : ∑ y ∈ s, w y * ⟪y, commonTangentNormal a b⟫
      = w 0 * ⟪(0 : Pt), commonTangentNormal a b⟫
        + w !₂[a + b, 0] * ⟪!₂[a + b, 0], commonTangentNormal a b⟫
        + ∑ y ∈ (s.erase 0).erase !₂[a + b, 0], w y * ⟪y, commonTangentNormal a b⟫ := by
    rw [← Finset.add_sum_erase s _ h0s, ← Finset.add_sum_erase _ _ hBs]
    ring
  have split_g : ∑ y ∈ s, w y * ⟪y - Q, h⁻¹ • (P - Q)⟫
      = w 0 * ⟪(0 : Pt) - Q, h⁻¹ • (P - Q)⟫
        + w !₂[a + b, 0] * ⟪!₂[a + b, 0] - Q, h⁻¹ • (P - Q)⟫
        + ∑ y ∈ (s.erase 0).erase !₂[a + b, 0], w y * ⟪y - Q, h⁻¹ • (P - Q)⟫ := by
    rw [← Finset.add_sum_erase s _ h0s, ← Finset.add_sum_erase _ _ hBs]
    ring
  have fP : ⟪P, commonTangentNormal a b⟫ = ∑ y ∈ s, w y * ⟪y, commonTangentNormal a b⟫ := by
    rw [← hcm, sum_inner]
    apply Finset.sum_congr rfl
    intro y _
    rw [real_inner_smul_left]
  have gP_sum : ⟪P - Q, h⁻¹ • (P - Q)⟫ = ∑ y ∈ s, w y * ⟪y - Q, h⁻¹ • (P - Q)⟫ := by
    have e1 : P - Q = ∑ y ∈ s, w y • (y - Q) := by
      have e2 : ∑ y ∈ s, w y • (y - Q)
          = (∑ y ∈ s, w y • y) - (∑ y ∈ s, w y) • Q := by
        rw [Finset.sum_smul, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro y _
        rw [smul_sub]
      rw [e2, hw1, one_smul, hcm]
    rw [e1, sum_inner]
    apply Finset.sum_congr rfl
    intro y _
    rw [real_inner_smul_left]
  have hf_bound : ∀ y ∈ (s.erase 0).erase !₂[a + b, 0], ⟪y, commonTangentNormal a b⟫ ≤ a := by
    intro y hy
    rcases hyCD y hy with rfl | rfl
    · exact fC
    · exact fD
  have hg_zero : ∀ y ∈ (s.erase 0).erase !₂[a + b, 0], ⟪y - Q, h⁻¹ • (P - Q)⟫ = 0 := by
    intro y hy
    rcases hyCD y hy with rfl | rfl
    · exact gC
    · exact gD
  have hw0nn : 0 ≤ w 0 := hw0 0 h0s
  have hwBnn : 0 ≤ w !₂[a + b, 0] := hw0 !₂[a + b, 0] (Finset.mem_of_mem_erase hBs)
  have hfb : ∑ y ∈ (s.erase 0).erase !₂[a + b, 0], w y * ⟪y, commonTangentNormal a b⟫
      ≤ (∑ y ∈ (s.erase 0).erase !₂[a + b, 0], w y) * a := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro y hy
    have hys : y ∈ s := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hy)
    exact mul_le_mul_of_nonneg_left (hf_bound y hy) (hw0 y hys)
  have hgsum0 : ∑ y ∈ (s.erase 0).erase !₂[a + b, 0], w y * ⟪y - Q, h⁻¹ • (P - Q)⟫ = 0 := by
    apply Finset.sum_eq_zero
    intro y hy
    rw [hg_zero y hy, mul_zero]
  have fbound : ⟪P, commonTangentNormal a b⟫ ≤ a - a * w 0 - b * w !₂[a + b, 0] := by
    rw [fP, split_f, f0, fB, mul_zero, zero_add]
    have hrest : ∑ y ∈ (s.erase 0).erase !₂[a + b, 0], w y = 1 - w 0 - w !₂[a + b, 0] := by
      linarith [split_w]
    rw [hrest] at hfb
    linarith [hfb]
  have key : h ≤ a * w 0 + b * w !₂[a + b, 0] := by
    have e := gP
    rw [gP_sum, split_g, hgsum0, add_zero] at e
    have h1 : w 0 * ⟪(0 : Pt) - Q, h⁻¹ • (P - Q)⟫ ≤ w 0 * a :=
      mul_le_mul_of_nonneg_left g0_le hw0nn
    have h2 : w !₂[a + b, 0] * ⟪!₂[a + b, 0] - Q, h⁻¹ • (P - Q)⟫ ≤ w !₂[a + b, 0] * b :=
      mul_le_mul_of_nonneg_left gB_le hwBnn
    linarith [h1, h2, e]
  have final : ⟪P, commonTangentNormal a b⟫ ≤ a - h := by linarith [fbound, key]
  have fPval : ⟪P, commonTangentNormal a b⟫
      = P 0 * ((a - b) / (a + b)) + P 1 * (2 * √(a * b) / (a + b)) := by
    rw [commonTangentNormal, inner_mk_right]
  rw [fPval] at final
  have e : (P 0 * ((a - b) / (a + b)) + P 1 * (2 * √(a * b) / (a + b))) * (a + b)
      = (a - b) * P 0 + 2 * √(a * b) * P 1 := by
    field_simp
  have hle : (P 0 * ((a - b) / (a + b)) + P 1 * (2 * √(a * b) / (a + b))) * (a + b)
      ≤ (a - h) * (a + b) := mul_le_mul_of_nonneg_right final habp.le
  rw [e] at hle
  linarith [hle]

/-- The two tangent-chord equations determine the first coordinate of `P`. -/
lemma px_eq {a b h px py : ℝ} (hab : (0 : ℝ) < a + b)
    (hp1 : px^2 + py^2 = (a + h)^2) (hp2 : (px - (a + b))^2 + py^2 = (b + h)^2) :
    px = a + h * (a - b) / (a + b) := by
  have hne : a + b ≠ 0 := ne_of_gt hab
  have key : 2 * (a + b) * px = (a + h)^2 - (b + h)^2 + (a + b)^2 := by
    linear_combination hp1 - hp2
  field_simp
  linarith [key]

/-- … and hence the second coordinate of `P` up to sign. -/
lemma py_sq {a b h px py : ℝ} (hab : (0 : ℝ) < a + b)
    (hp1 : px^2 + py^2 = (a + h)^2) (hpx : px = a + h * (a - b) / (a + b)) :
    py^2 = 4 * a * b * h * (a + b + h) / (a + b)^2 := by
  have hne : a + b ≠ 0 := ne_of_gt hab
  have e1 : py^2 = (a + h)^2 - px^2 := by linarith [hp1]
  rw [e1, hpx]
  field_simp
  ring

/-- Rewriting `√(a*b) * py` using the formula for `py^2`. -/
lemma sqrt_ab_py {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {h py : ℝ} (hh : 0 < h)
    (hpy : 0 < py) (hpy2 : py^2 = 4 * a * b * h * (a + b + h) / (a + b)^2) :
    √(a * b) * py = 2 * a * b * √(h * (a + b + h)) / (a + b) := by
  have hab : (0 : ℝ) < a * b := mul_pos ha hb
  have habp : (0 : ℝ) < a + b := add_pos ha hb
  have hne : a + b ≠ 0 := ne_of_gt habp
  have step1 : √(a * b) * py = √(a * b * (py^2)) := by
    rw [Real.sqrt_mul hab.le (py^2), Real.sqrt_sq hpy.le]
  rw [step1, hpy2]
  have e5 : a * b * (4 * a * b * h * (a + b + h) / (a + b)^2)
      = (2 * a * b * √(h * (a + b + h)) / (a + b))^2 := by
    rw [div_pow, mul_pow, mul_pow,
      Real.sq_sqrt (show (0 : ℝ) ≤ h * (a + b + h) by positivity)]
    field_simp
    ring
  rw [e5, Real.sqrt_sq (by positivity)]

/-- The function `G(x) = x(a^2+b^2) + 2ab√(x(a+b+x))` is strictly increasing
on positive reals. -/
lemma G_lt {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {x y : ℝ} (hx : 0 < x) (hxy : x < y) :
    x * (a^2 + b^2) + 2 * a * b * √(x * (a + b + x))
      < y * (a^2 + b^2) + 2 * a * b * √(y * (a + b + y)) := by
  have h1 : x * (a^2 + b^2) < y * (a^2 + b^2) := by
    apply mul_lt_mul_of_pos_right hxy
    positivity
  have h2 : √(x * (a + b + x)) < √(y * (a + b + y)) := by
    apply Real.sqrt_lt_sqrt (by positivity)
    have hy : 0 < y := by linarith
    have hprod : (0 : ℝ) < (y - x) * (a + b + x + y) := by
      apply mul_pos (sub_pos.mpr hxy)
      positivity
    nlinarith [hprod]
  have h3 : 2 * a * b * √(x * (a + b + x)) < 2 * a * b * √(y * (a + b + y)) := by
    apply mul_lt_mul_of_pos_left h2
    positivity
  linarith

/-- The extremal value: `G(h₀) = ab(a+b)` for `h₀ = ab/(√a+√b)²`. -/
lemma G_h0 {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (a * b / (√a + √b)^2) * (a^2 + b^2)
      + 2 * a * b * √((a * b / (√a + √b)^2) * (a + b + (a * b / (√a + √b)^2)))
      = a * b * (a + b) := by
  have hspos : 0 < √a + √b := by positivity
  have hs2ne : (√a + √b)^2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hspos)
  have hs4ne : (√a + √b)^4 ≠ 0 := pow_ne_zero 4 (ne_of_gt hspos)
  have hr2 : √(a * b)^2 = a * b := Real.sq_sqrt (by positivity)
  have hs2 : (√a + √b)^2 = a + b + 2 * √(a * b) := by
    have e3 : √a * √b = √(a * b) := (Real.sqrt_mul ha.le b).symm
    rw [add_sq, Real.sq_sqrt ha.le, Real.sq_sqrt hb.le]
    linear_combination 2 * e3
  have e4 : (a + b + √(a * b))^2 = (a + b) * (a + b + 2 * √(a * b)) + a * b := by
    linear_combination hr2
  have key1 : (a * b / (√a + √b)^2) * (a + b + (a * b / (√a + √b)^2))
      = a * b * (a + b + √(a * b))^2 / (√a + √b)^4 := by
    have step : (a * b / (√a + √b)^2) * (a + b + (a * b / (√a + √b)^2))
        = (a * b * (a + b) * (√a + √b)^2 + (a * b)^2) / (√a + √b)^4 := by
      field_simp
    have enum : a * b * (a + b) * (√a + √b)^2 + (a * b)^2
        = a * b * ((a + b) * (a + b + 2 * √(a * b)) + a * b) := by
      linear_combination (a * b * (a + b)) * hs2
    rw [step, e4, enum]
  have key2 : √((a * b / (√a + √b)^2) * (a + b + (a * b / (√a + √b)^2)))
      = √(a * b) * (a + b + √(a * b)) / (√a + √b)^2 := by
    have e5 : a * b * (a + b + √(a * b))^2 / (√a + √b)^4
        = (√(a * b) * (a + b + √(a * b)) / (√a + √b)^2)^2 := by
      rw [div_pow, mul_pow, hr2, show (√a + √b)^4 = ((√a + √b)^2)^2 by ring]
    rw [key1, e5]
    exact Real.sqrt_sq (by positivity)
  rw [key2]
  have step2 : (a * b / (√a + √b)^2) * (a^2 + b^2)
      + 2 * a * b * (√(a * b) * (a + b + √(a * b)) / (√a + √b)^2)
      = (a * b * (a^2 + b^2) + 2 * a * b * √(a * b) * (a + b + √(a * b))) / (√a + √b)^2 := by
    field_simp
  rw [step2, div_eq_iff hs2ne]
  linear_combination (-(a * b * (a + b))) * hs2 + (2 * a * b) * hr2

/-- The final inequality from the estimate `G(h) ≤ ab(a+b)`. -/
lemma final_ineq {a b h : ℝ} (ha : 0 < a) (hb : 0 < b) (hh : 0 < h)
    (hG : h * (a^2 + b^2) + 2 * a * b * √(h * (a + b + h)) ≤ a * b * (a + b)) :
    1 / √h ≥ 1 / √a + 1 / √b := by
  have h0pos : 0 < a * b / (√a + √b)^2 := by positivity
  have hle : h ≤ a * b / (√a + √b)^2 := by
    by_contra hcon
    push Not at hcon
    have hlt := G_lt ha hb h0pos hcon
    rw [G_h0 ha hb] at hlt
    linarith
  have hsqrth : √h ≤ √(a * b / (√a + √b)^2) := Real.sqrt_le_sqrt hle
  have hinv : 1 / √(a * b / (√a + √b)^2) ≤ 1 / √h := by
    apply one_div_le_one_div_of_le (Real.sqrt_pos.mpr hh) hsqrth
  have heq : 1 / √(a * b / (√a + √b)^2) = 1 / √a + 1 / √b := by
    have hs : 0 < √a + √b := by positivity
    have e1 : √(a * b / (√a + √b)^2) = √(a * b) / (√a + √b) := by
      rw [Real.sqrt_div (by positivity), Real.sqrt_sq hs.le]
    rw [e1, one_div_div, Real.sqrt_mul ha.le b]
    field_simp [Real.sqrt_ne_zero'.mpr ha, Real.sqrt_ne_zero'.mpr hb]
    ring
  rw [heq] at hinv
  exact hinv

snip end

problem imo1989_p4
    (a b h : ℝ) (ha : 0 < a) (hb : 0 < b) (hh : 0 < h)
    (P C D : Pt)
    (hpy : 0 < P 1)
    (hAP : dist P 0 = a + h)
    (hBP : dist P !₂[a + b, 0] = b + h)
    (hAD : dist D 0 = a)
    (hBC : dist C !₂[a + b, 0] = b)
    (hdist : dist P (orthogonalProjection line[ℝ, C, D] P : Pt) = h)
    (hP : P ∈ interior (convexHull ℝ (({0, !₂[a + b, 0], C, D} : Finset Pt) : Set Pt))) :
    1 / √h ≥ 1 / √a + 1 / √b := by
  have hconf : (a - b) * P 0 + 2 * √(a * b) * P 1 ≤ (a - h) * (a + b) :=
    confine ha hb hh P C D hAD hBC hdist hP
  have habp : (0 : ℝ) < a + b := by positivity
  have hne : a + b ≠ 0 := ne_of_gt habp
  rw [dist_eq] at hAP hBP
  simp only [WithLp.ofLp_zero, Pi.zero_apply, sub_zero] at hAP
  have hp1 : P 0 ^2 + P 1 ^2 = (a + h)^2 := by
    have h2 := congrArg (· ^ 2) hAP
    rwa [Real.sq_sqrt (by positivity)] at h2
  have hB0 : (!₂[a + b, 0] : Pt) 0 = a + b := by simp
  have hB1 : (!₂[a + b, 0] : Pt) 1 = (0 : ℝ) := by simp
  rw [hB0, hB1, sub_zero] at hBP
  have hp2 : (P 0 - (a + b))^2 + P 1 ^2 = (b + h)^2 := by
    have h2 := congrArg (· ^ 2) hBP
    rwa [Real.sq_sqrt (by positivity)] at h2
  have hpx : P 0 = a + h * (a - b) / (a + b) := px_eq habp hp1 hp2
  have hpy2 : P 1 ^2 = 4 * a * b * h * (a + b + h) / (a + b)^2 := py_sq habp hp1 hpx
  have e1 : √(a * b) * P 1 = 2 * a * b * √(h * (a + b + h)) / (a + b) :=
    sqrt_ab_py ha hb hh hpy hpy2
  -- Now expand the confinement hypothesis.
  have hconf2 : (a + b) * ((a - b) * P 0 + 2 * √(a * b) * P 1)
      ≤ (a + b) * ((a - h) * (a + b)) :=
    mul_le_mul_of_nonneg_left hconf habp.le
  have e2 : (a + b) * ((a - b) * P 0 + 2 * √(a * b) * P 1)
      = (a + b) * (a - b) * P 0 + 2 * (a + b) * (√(a * b) * P 1) := by ring
  have e3 : 2 * (a + b) * (√(a * b) * P 1) = 4 * a * b * √(h * (a + b + h)) := by
    rw [e1]
    field_simp
    ring
  rw [e2, e3] at hconf2
  have e4 : (a + b) * (a - b) * P 0 = a * (a^2 - b^2) + h * (a - b)^2 := by
    rw [hpx]
    field_simp
    ring
  rw [e4] at hconf2
  have e5 : (a + b) * ((a - h) * (a + b)) = (a - h) * (a + b)^2 := by ring
  rw [e5] at hconf2
  have hG : h * (a^2 + b^2) + 2 * a * b * √(h * (a + b + h)) ≤ a * b * (a + b) := by
    linarith [hconf2]
  exact final_ineq ha hb hh hG

end Imo1989P4
