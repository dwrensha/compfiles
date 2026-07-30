/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Tactic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Olympiad 1981, Problem 5

Three circles of equal radius have a common point $O$ and lie inside a given
triangle. Each circle touches a pair of sides of the triangle. Prove that the
incenter and the circumcenter of the triangle are collinear with the point $O$.

# Formal statement

Let $A$, $B$, $C$ be the vertices of the (non-degenerate) triangle in the
Euclidean plane, let $I$ be its incenter, $K$ its circumcenter and $\rho$ its
inradius. The center $D$ of a circle of radius $r$ touching $AB$ and $AC$ lies
on the internal angle bisector at $A$, i.e. on the ray from $A$ through $I$;
moreover its distance to the line $AB$ equals $r$. Since the distance to the
line $AB$ varies linearly along the ray from $A$ (where it is $0$) to $I$
(where it is $\rho$), we have $D = A + (r/\rho)(I - A)$. The same argument at
$B$ and $C$ gives $E = B + (r/\rho)(I - B)$ and $F = C + (r/\rho)(I - C)$ for
the other two centers. Hence, with $s := 1 - r/\rho$, the three centers $D$,
$E$, $F$ are the images of the vertices under the homothety
$X \mapsto s • X + (1 - s) • I$ centered at $I$. The three circles are
distinct and lie inside the triangle, so $0 < r < \rho$ and in particular
$s \neq 0$. The common point $O$ of the three circles is equidistant from the
centers $D$, $E$, $F$.

The statement below therefore takes as data: a non-collinear triple $A$, $B$,
$C$ of points of the plane, points $I$ (the incenter) and $K$ (a point
equidistant from the vertices, i.e. the circumcenter), a nonzero scalar $s$,
the centers $D$, $E$, $F$ given as the images of $A$, $B$, $C$ under the
homothety of ratio $s$ about $I$, and a point $O$ equidistant from $D$, $E$,
$F$. The conclusion is that $O$, $I$ and $K$ are collinear.

# Solution

The homothety $X \mapsto s • X + (1 - s) • I$ multiplies all distances by
$|s|$, so the image $K' = s • K + (1 - s) • I$ of the circumcenter is
equidistant from $D$, $E$, $F$: it is a circumcenter of the triangle $DEF$.
In the plane, a non-degenerate triangle has a unique circumcenter: two points
both equidistant from $D$, $E$, $F$ must coincide (their difference vector is
orthogonal to $E - D$ and $F - D$, whose determinant is nonzero). Hence
$O = K'$, and $K' - I = s • (K - I)$ shows that $O$ lies on the line $IK$.
-/

namespace Imo1981P5

/-- The Euclidean plane, coordinatized as `ℝ²`. -/
abbrev Pt := Fin 2 → ℝ

/-- The squared Euclidean distance between two points of the plane. -/
def distSq (X Y : Pt) : ℝ := (X 0 - Y 0) ^ 2 + (X 1 - Y 1) ^ 2

/-- The Euclidean distance between two points of the plane. -/
noncomputable def Dist (X Y : Pt) : ℝ := Real.sqrt (distSq X Y)

/-- The determinant of two plane vectors: the signed area of the
parallelogram they span. -/
def det (u v : Pt) : ℝ := u 0 * v 1 - u 1 * v 0

snip begin

/-- If the determinant of `B - A` and `C - A` vanishes, then the points `A`,
`B`, `C` are collinear. -/
lemma collinear_of_det_eq_zero {A B C : Pt} (h : det (B - A) (C - A) = 0) :
    Collinear ℝ ({A, B, C} : Set Pt) := by
  by_cases hAB : B = A
  · rw [hAB, Set.insert_idem]
    exact collinear_pair ℝ A C
  · have hu : B - A ≠ 0 := sub_ne_zero.mpr hAB
    have h' : (B - A) 0 * (C - A) 1 = (B - A) 1 * (C - A) 0 := by
      unfold det at h
      linarith
    obtain ⟨t, ht⟩ : ∃ t : ℝ, C - A = t • (B - A) := by
      by_cases h0 : (B - A) 0 ≠ 0
      · refine ⟨(C - A) 0 / (B - A) 0, ?_⟩
        rw [funext_iff, Fin.forall_fin_two]
        refine ⟨?_, ?_⟩
        · rw [Pi.smul_apply, smul_eq_mul, div_mul_cancel₀ _ h0]
        · rw [Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div, eq_div_iff_mul_eq h0]
          linarith [h']
      · have h0' : (B - A) 0 = 0 := not_ne_iff.mp h0
        have h1 : (B - A) 1 ≠ 0 := by
          intro hc1
          exact hu (funext (Fin.forall_fin_two.mpr ⟨h0', hc1⟩))
        refine ⟨(C - A) 1 / (B - A) 1, ?_⟩
        rw [funext_iff, Fin.forall_fin_two]
        refine ⟨?_, ?_⟩
        · rw [Pi.smul_apply, smul_eq_mul, h0', mul_zero]
          have h'' : (B - A) 1 * (C - A) 0 = 0 := by
            rw [← h', h0', zero_mul]
          exact (mul_eq_zero.mp h'').resolve_left h1
        · rw [Pi.smul_apply, smul_eq_mul, div_mul_cancel₀ _ h1]
    rw [collinear_iff_of_mem (Set.mem_insert A {B, C})]
    refine ⟨B - A, fun p hp ↦ ?_⟩
    rw [Set.mem_insert_iff, Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨0, by rw [zero_smul, zero_vadd]⟩
    · exact ⟨1, by rw [one_smul, vadd_eq_add, sub_add_cancel]⟩
    · exact ⟨t, by rw [vadd_eq_add, ← ht, sub_add_cancel]⟩

/-- If `A`, `B`, `C` are not collinear, the determinant of `B - A` and
`C - A` is nonzero. -/
lemma det_ne_zero_of_not_collinear {A B C : Pt}
    (h : ¬ Collinear ℝ ({A, B, C} : Set Pt)) :
    det (B - A) (C - A) ≠ 0 :=
  fun hd ↦ h (collinear_of_det_eq_zero hd)

/-- The difference of the images of two points under the homothety of ratio
`s` about `I` is `s` times the difference of the points. -/
lemma homothety_sub (s : ℝ) (I X Y : Pt) :
    s • X + (1 - s) • I - (s • Y + (1 - s) • I) = s • (X - Y) := by
  module

/-- The homothety of ratio `s` about `I` multiplies all distances by `|s|`. -/
lemma Dist_homothety (s : ℝ) (I X Y : Pt) :
    Dist (s • X + (1 - s) • I) (s • Y + (1 - s) • I) = |s| * Dist X Y := by
  have h : distSq (s • X + (1 - s) • I) (s • Y + (1 - s) • I)
      = s ^ 2 * distSq X Y := by
    unfold distSq
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  unfold Dist
  rw [h, Real.sqrt_mul (sq_nonneg s), Real.sqrt_sq_eq_abs]

/-- Scaling both arguments of the determinant by `s` multiplies it by
`s ^ 2`. -/
lemma det_smul_smul (s : ℝ) (u v : Pt) :
    det (s • u) (s • v) = s ^ 2 * det u v := by
  unfold det
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- Uniqueness of the circumcenter of a non-degenerate plane triangle: two
points that are both equidistant from the three vertices coincide. -/
lemma eq_of_dist_eq {D E F P Q : Pt}
    (hdet : det (E - D) (F - D) ≠ 0)
    (hP : Dist P D = Dist P E ∧ Dist P E = Dist P F)
    (hQ : Dist Q D = Dist Q E ∧ Dist Q E = Dist Q F) :
    P = Q := by
  have dsq : ∀ X Y : Pt, Dist X Y ^ 2 = distSq X Y := by
    intro X Y
    have hnn : 0 ≤ distSq X Y := by
      unfold distSq
      positivity
    unfold Dist
    exact Real.sq_sqrt hnn
  have e1 : distSq P D = distSq P E := by
    have h := congrArg (fun x ↦ x ^ 2) hP.1
    rwa [dsq, dsq] at h
  have e2 : distSq P E = distSq P F := by
    have h := congrArg (fun x ↦ x ^ 2) hP.2
    rwa [dsq, dsq] at h
  have e3 : distSq Q D = distSq Q E := by
    have h := congrArg (fun x ↦ x ^ 2) hQ.1
    rwa [dsq, dsq] at h
  have e4 : distSq Q E = distSq Q F := by
    have h := congrArg (fun x ↦ x ^ 2) hQ.2
    rwa [dsq, dsq] at h
  have g1 : (P 0 - Q 0) * (E 0 - D 0) + (P 1 - Q 1) * (E 1 - D 1) = 0 := by
    unfold distSq at e1 e3
    linarith
  have g2 : (P 0 - Q 0) * (F 0 - D 0) + (P 1 - Q 1) * (F 1 - D 1) = 0 := by
    unfold distSq at e2 e4
    linarith
  have hdet' : (E 0 - D 0) * (F 1 - D 1) - (E 1 - D 1) * (F 0 - D 0) ≠ 0 := by
    unfold det at hdet
    simpa [Pi.sub_apply] using hdet
  have h0 : P 0 - Q 0 = 0 := by
    have hmul : (P 0 - Q 0) *
        ((E 0 - D 0) * (F 1 - D 1) - (E 1 - D 1) * (F 0 - D 0)) = 0 := by
      linear_combination (F 1 - D 1) * g1 - (E 1 - D 1) * g2
    exact (mul_eq_zero.mp hmul).resolve_right hdet'
  have h1 : P 1 - Q 1 = 0 := by
    have hmul : (P 1 - Q 1) *
        ((E 0 - D 0) * (F 1 - D 1) - (E 1 - D 1) * (F 0 - D 0)) = 0 := by
      linear_combination (E 0 - D 0) * g2 - (F 0 - D 0) * g1
    exact (mul_eq_zero.mp hmul).resolve_right hdet'
  have h0' : P 0 = Q 0 := sub_eq_zero.mp h0
  have h1' : P 1 = Q 1 := sub_eq_zero.mp h1
  exact funext (Fin.forall_fin_two.mpr ⟨h0', h1'⟩)

snip end

problem imo1981_p5 {A B C D E F I O K : Pt} {s : ℝ}
    (hnc : ¬ Collinear ℝ ({A, B, C} : Set Pt))
    (hs : s ≠ 0)
    (hD : D = s • A + (1 - s) • I)
    (hE : E = s • B + (1 - s) • I)
    (hF : F = s • C + (1 - s) • I)
    (hK : Dist K A = Dist K B ∧ Dist K B = Dist K C)
    (hO : Dist O D = Dist O E ∧ Dist O E = Dist O F) :
    Collinear ℝ ({O, I, K} : Set Pt) := by
  -- The homothetic image of the circumcenter is equidistant from `D`, `E`,
  -- `F`, hence is a circumcenter of the triangle `DEF`.
  have h1 : Dist (s • K + (1 - s) • I) D = |s| * Dist K A := by
    rw [hD, Dist_homothety]
  have h2 : Dist (s • K + (1 - s) • I) E = |s| * Dist K B := by
    rw [hE, Dist_homothety]
  have h3 : Dist (s • K + (1 - s) • I) F = |s| * Dist K C := by
    rw [hF, Dist_homothety]
  have hK' : Dist (s • K + (1 - s) • I) D = Dist (s • K + (1 - s) • I) E ∧
      Dist (s • K + (1 - s) • I) E = Dist (s • K + (1 - s) • I) F := by
    rw [h1, h2, h3]
    exact ⟨by rw [hK.1], by rw [hK.2]⟩
  -- The centers `D`, `E`, `F` form a non-degenerate triangle.
  have hdetABC : det (B - A) (C - A) ≠ 0 := det_ne_zero_of_not_collinear hnc
  have hsub1 : E - D = s • (B - A) := by rw [hE, hD, homothety_sub]
  have hsub2 : F - D = s • (C - A) := by rw [hF, hD, homothety_sub]
  have hdetDEF : det (E - D) (F - D) ≠ 0 := by
    rw [hsub1, hsub2, det_smul_smul]
    exact mul_ne_zero (pow_ne_zero 2 hs) hdetABC
  -- Uniqueness of the circumcenter forces `O` to be the image of `K`.
  have hO' : O = s • K + (1 - s) • I := eq_of_dist_eq hdetDEF hO hK'
  -- Hence `O` lies on the line through `I` and `K`.
  rw [hO']
  rw [collinear_iff_of_mem (Set.mem_insert_of_mem _ (Set.mem_insert I {K}))]
  refine ⟨K - I, fun p hp ↦ ?_⟩
  rw [Set.mem_insert_iff, Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl
  · exact ⟨s, by rw [vadd_eq_add]; module⟩
  · exact ⟨0, by rw [zero_smul, zero_vadd]⟩
  · exact ⟨1, by rw [one_smul, vadd_eq_add, sub_add_cancel]⟩

end Imo1981P5
