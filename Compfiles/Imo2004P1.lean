/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Euclidean.Sphere.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Ring
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Olympiad 2004, Problem 1

Let ABC be an acute-angled triangle with AB ≠ AC. The circle with diameter BC
intersects the sides AB and AC at M and N respectively. Denote by O the
midpoint of the side BC. The bisectors of the angles ∠BAC and ∠MON intersect
at R. Prove that the circumcircles of the triangles BMR and CNR have a common
point lying on the side BC.

# Formalization notes

The proof is a direct coordinate computation; for the classical synthetic
solution see e.g. Evan Chen's IMO 2004 notes.
-/

namespace Imo2004P1

open EuclideanGeometry

snip begin

/-- Distance between two explicitly given points of the Euclidean plane. -/
lemma dist2 (x1 y1 x2 y2 : ℝ) :
    dist (!₂[x1, y1] : EuclideanSpace ℝ (Fin 2)) !₂[x2, y2]
      = Real.sqrt ((x1 - x2) ^ 2 + (y1 - y2) ^ 2) := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Real.dist_eq, sq_abs]

/-- The vertex `B`, with `AB` in direction `(p, q)`. -/
def ptB (p q c : ℝ) : EuclideanSpace ℝ (Fin 2) := !₂[c * p, c * q]

/-- The vertex `C`, with `AC` in direction `(p, -q)`. -/
def ptC (p q b : ℝ) : EuclideanSpace ℝ (Fin 2) := !₂[b * p, -(b * q)]

/-- The foot of the altitude from `C` on `AB`, i.e. the second intersection of
line `AB` with the circle of diameter `BC`. -/
noncomputable def ptM (p q b : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  !₂[b * (p ^ 2 - q ^ 2) / (p ^ 2 + q ^ 2) * p, b * (p ^ 2 - q ^ 2) / (p ^ 2 + q ^ 2) * q]

/-- The foot of the altitude from `B` on `AC`, i.e. the second intersection of
line `AC` with the circle of diameter `BC`. -/
noncomputable def ptN (p q c : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  !₂[c * (p ^ 2 - q ^ 2) / (p ^ 2 + q ^ 2) * p, -(c * (p ^ 2 - q ^ 2) / (p ^ 2 + q ^ 2) * q)]

/-- The intersection of the bisectors of `∠BAC` and `∠MON`. -/
noncomputable def ptR (p q b c : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  !₂[(b + c) * (p ^ 2 - q ^ 2) / (2 * p), 0]

/-- The candidate common point of the two circumcircles on side `BC`: the meet
of the internal bisector of `∠BAC` with `BC`. -/
noncomputable def ptK (p _q b c : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  !₂[2 * b * c * p / (b + c), 0]

/-- The circumcenter of triangle `BMR`. -/
noncomputable def ctrBMR (p q b c : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  !₂[(b ^ 2 * p ^ 2 - b ^ 2 * q ^ 2 + 6 * b * c * p ^ 2 - 2 * b * c * q ^ 2
        + c ^ 2 * p ^ 2 - c ^ 2 * q ^ 2) / (4 * p * (b + c)),
      (b ^ 2 * p ^ 2 - b ^ 2 * q ^ 2 - 2 * b * c * p ^ 2 + 2 * b * c * q ^ 2
        + c ^ 2 * p ^ 2 + 3 * c ^ 2 * q ^ 2) / (4 * q * (b + c))]

/-- The circumcenter of triangle `CNR`. -/
noncomputable def ctrCNR (p q b c : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  !₂[(b ^ 2 * p ^ 2 - b ^ 2 * q ^ 2 + 6 * b * c * p ^ 2 - 2 * b * c * q ^ 2
        + c ^ 2 * p ^ 2 - c ^ 2 * q ^ 2) / (4 * p * (b + c)),
      -((b ^ 2 * p ^ 2 + 3 * b ^ 2 * q ^ 2 - 2 * b * c * p ^ 2 + 2 * b * c * q ^ 2
        + c ^ 2 * p ^ 2 - c ^ 2 * q ^ 2) / (4 * q * (b + c)))]

/-- Four points are cospherical once three of them have the same distance to a
common center as the fourth. -/
lemma cospherical_of_dist_eq {O W X Y Z : EuclideanSpace ℝ (Fin 2)}
    (hX : dist X O = dist W O) (hY : dist Y O = dist W O) (hZ : dist Z O = dist W O) :
    Cospherical ({W, X, Y, Z} : Set (EuclideanSpace ℝ (Fin 2))) := by
  refine ⟨O, dist W O, fun P hP => ?_⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hP
  rcases hP with rfl | rfl | rfl | rfl
  · rfl
  · exact hX
  · exact hY
  · exact hZ

/-- Equality of squared distances to a common center `O = (o₁, o₂)`, rewritten
to a form that is linear in the center coordinates (the `o₁² + o₂²` terms
cancel). Checking the equation in this form keeps the polynomials that
`field_simp` and `ring` produce much smaller than for the raw form. -/
lemma sq_dist_eq_iff (x1 x2 w1 w2 o1 o2 : ℝ) :
    (x1 - o1) ^ 2 + (x2 - o2) ^ 2 = (w1 - o1) ^ 2 + (w2 - o2) ^ 2 ↔
    x1 ^ 2 + x2 ^ 2 - (w1 ^ 2 + w2 ^ 2) = 2 * (o1 * (x1 - w1) + o2 * (x2 - w2)) := by
  constructor <;> intro h <;> linear_combination h

lemma dist_ptM_ctrBMR {p q b c : ℝ} (hp : p ≠ 0) (hq : q ≠ 0) (hn : p ^ 2 + q ^ 2 ≠ 0)
    (hbc : b + c ≠ 0) :
    dist (ptM p q b) (ctrBMR p q b c) = dist (ptB p q c) (ctrBMR p q b c) := by
  simp only [ptM, ptB, ctrBMR, dist2]
  congr 1
  rw [sq_dist_eq_iff]
  field_simp [hp, hq, hn, hbc]
  ring

lemma dist_ptR_ctrBMR {p q b c : ℝ} (hp : p ≠ 0) (hq : q ≠ 0) (hbc : b + c ≠ 0) :
    dist (ptR p q b c) (ctrBMR p q b c) = dist (ptB p q c) (ctrBMR p q b c) := by
  simp only [ptR, ptB, ctrBMR, dist2]
  congr 1
  rw [sq_dist_eq_iff]
  field_simp [hp, hq, hbc]
  ring

lemma dist_ptK_ctrBMR {p q b c : ℝ} (hp : p ≠ 0) (hq : q ≠ 0) (hbc : b + c ≠ 0) :
    dist (ptK p q b c) (ctrBMR p q b c) = dist (ptB p q c) (ctrBMR p q b c) := by
  simp only [ptK, ptB, ctrBMR, dist2]
  congr 1
  rw [sq_dist_eq_iff]
  field_simp [hp, hq, hbc]
  ring

lemma dist_ptN_ctrCNR {p q b c : ℝ} (hp : p ≠ 0) (hq : q ≠ 0) (hn : p ^ 2 + q ^ 2 ≠ 0)
    (hbc : b + c ≠ 0) :
    dist (ptN p q c) (ctrCNR p q b c) = dist (ptC p q b) (ctrCNR p q b c) := by
  simp only [ptN, ptC, ctrCNR, dist2]
  congr 1
  rw [sq_dist_eq_iff]
  field_simp [hp, hq, hn, hbc]
  ring

lemma dist_ptR_ctrCNR {p q b c : ℝ} (hp : p ≠ 0) (hq : q ≠ 0) (hbc : b + c ≠ 0) :
    dist (ptR p q b c) (ctrCNR p q b c) = dist (ptC p q b) (ctrCNR p q b c) := by
  simp only [ptR, ptC, ctrCNR, dist2]
  congr 1
  rw [sq_dist_eq_iff]
  field_simp [hp, hq, hbc]
  ring

lemma dist_ptK_ctrCNR {p q b c : ℝ} (hp : p ≠ 0) (hq : q ≠ 0) (hbc : b + c ≠ 0) :
    dist (ptK p q b c) (ctrCNR p q b c) = dist (ptC p q b) (ctrCNR p q b c) := by
  simp only [ptK, ptC, ctrCNR, dist2]
  congr 1
  rw [sq_dist_eq_iff]
  field_simp [hp, hq, hbc]
  ring

/-- The points `B`, `M`, `R`, `K` are concyclic. -/
lemma cospherical_BMRK {p q b c : ℝ} (hp : p ≠ 0) (hq : q ≠ 0) (hn : p ^ 2 + q ^ 2 ≠ 0)
    (hbc : b + c ≠ 0) :
    Cospherical ({ptB p q c, ptM p q b, ptR p q b c, ptK p q b c}
      : Set (EuclideanSpace ℝ (Fin 2))) :=
  cospherical_of_dist_eq (dist_ptM_ctrBMR hp hq hn hbc) (dist_ptR_ctrBMR hp hq hbc)
    (dist_ptK_ctrBMR hp hq hbc)

/-- The points `C`, `N`, `R`, `K` are concyclic. -/
lemma cospherical_CNRK {p q b c : ℝ} (hp : p ≠ 0) (hq : q ≠ 0) (hn : p ^ 2 + q ^ 2 ≠ 0)
    (hbc : b + c ≠ 0) :
    Cospherical ({ptC p q b, ptN p q c, ptR p q b c, ptK p q b c}
      : Set (EuclideanSpace ℝ (Fin 2))) :=
  cospherical_of_dist_eq (dist_ptN_ctrCNR hp hq hn hbc) (dist_ptR_ctrCNR hp hq hbc)
    (dist_ptK_ctrCNR hp hq hbc)

/-- The point `K` lies (weakly) between `B` and `C`: it is the meet of the
internal bisector of `∠BAC` with the side `BC`. -/
lemma wbtw_BKC {p q b c : ℝ} (hb : 0 < b) (hc : 0 < c) :
    Wbtw ℝ (ptB p q c) (ptK p q b c) (ptC p q b) := by
  have hbc : (0 : ℝ) < b + c := by positivity
  refine ⟨c / (b + c), ⟨by positivity, by rw [div_le_one hbc]; linarith [hb.le]⟩, ?_⟩
  rw [AffineMap.lineMap_apply]
  simp only [vsub_eq_sub, vadd_eq_add, ptB, ptC, ptK]
  ext i
  fin_cases i <;>
    simp [PiLp.smul_apply, PiLp.add_apply, PiLp.sub_apply, smul_eq_mul] <;>
    field_simp [ne_of_gt hbc] <;>
    ring

snip end

problem imo2004_p1 (p q b c : ℝ) (hp : 0 < p) (hq : 0 < q) (hpq : q < p)
    (hb : 0 < b) (hc : 0 < c) (hbc : b ≠ c)
    (hB : b * (p ^ 2 - q ^ 2) < c * (p ^ 2 + q ^ 2))
    (hC : c * (p ^ 2 - q ^ 2) < b * (p ^ 2 + q ^ 2)) :
    ∃ K : EuclideanSpace ℝ (Fin 2),
      Wbtw ℝ (ptB p q c) K (ptC p q b) ∧
      Cospherical ({ptB p q c, ptM p q b, ptR p q b c, K}
        : Set (EuclideanSpace ℝ (Fin 2))) ∧
      Cospherical ({ptC p q b, ptN p q c, ptR p q b c, K}
        : Set (EuclideanSpace ℝ (Fin 2))) := by
  have hp' : p ≠ 0 := ne_of_gt hp
  have hq' : q ≠ 0 := ne_of_gt hq
  have hn' : p ^ 2 + q ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have hbc' : b + c ≠ 0 := ne_of_gt (by positivity)
  exact ⟨ptK p q b c, wbtw_BKC hb hc, cospherical_BMRK hp' hq' hn' hbc',
    cospherical_CNRK hp' hq' hn' hbc'⟩


end Imo2004P1
