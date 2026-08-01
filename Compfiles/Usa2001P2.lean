/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# USA Mathematical Olympiad 2001, Problem 2

The incircle of the triangle PBC touches BC at U and PC at V.
The point S on BC is such that BS = CU. PS meets the incircle at
two points. The nearer to P is Q. Take W on PC such that PW = CV.
Let BW and PS meet at R. Show that PQ = RS.

# Formalization notes

The problem is formalized in coordinates. For the classical synthetic
solution see e.g. https://prase.cz/kalva/usa/usoln/usol012.html .
-/

namespace Usa2001P2

/-- The Euclidean plane. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- The semiperimeter of a triangle with side lengths `p`, `b`, `c`. -/
noncomputable def s (p b c : ℝ) : ℝ := (p + b + c) / 2

/-- With `B = (0, 0)` and `C = (p, 0)`, the x-coordinate of the point `P`
with `|PB| = c` and `|PC| = b`. -/
noncomputable def px (p b c : ℝ) : ℝ := (c ^ 2 + p ^ 2 - b ^ 2) / (2 * p)

/-- The (positive) y-coordinate of `P`. -/
noncomputable def py (p b c : ℝ) : ℝ := Real.sqrt (c ^ 2 - (px p b c) ^ 2)

/-- Vertex `B`, placed at the origin. -/
noncomputable def Bp : Plane := !₂[0, 0]

/-- Vertex `C`, placed on the positive x-axis with `|BC| = p`. -/
noncomputable def Cp (p : ℝ) : Plane := !₂[p, 0]

/-- Vertex `P`, placed above the x-axis. -/
noncomputable def Pp (p b c : ℝ) : Plane := !₂[px p b c, py p b c]

/-- The touchpoint of the incircle with `BC`; here `BU = s - b`, `CU = s - c`. -/
noncomputable def Up (p b c : ℝ) : Plane := !₂[s p b c - b, 0]

/-- The touchpoint of the incircle with `PC`; here `CV = s - c`. -/
noncomputable def Vp (p b c : ℝ) : Plane :=
  Cp p + ((s p b c - c) / b) • (Pp p b c - Cp p)

/-- The point `S` on `BC` with `BS = CU = s - c`. -/
noncomputable def Sp (p b c : ℝ) : Plane := !₂[s p b c - c, 0]

/-- The point `W` on `PC` with `PW = s - c = CV`. -/
noncomputable def Wp (p b c : ℝ) : Plane :=
  Pp p b c + ((s p b c - c) / b) • (Cp p - Pp p b c)

/-- The inradius `r = area / s`. -/
noncomputable def rad (p b c : ℝ) : ℝ := p * py p b c / (2 * s p b c)

/-- The incenter: above `U` at height `r`. -/
noncomputable def Ip (p b c : ℝ) : Plane := !₂[s p b c - b, rad p b c]

/-- The parameter of `Q` on the line `PS`: `Q = P + t₁ • (S - P)`. -/
noncomputable def t1 (p b c : ℝ) : ℝ := (s p b c - p) / s p b c

/-- The squared distance `|PS|²`. -/
noncomputable def dPS2 (p b c : ℝ) : ℝ :=
  (s p b c - c - px p b c) ^ 2 + (py p b c) ^ 2

/-- The parameter of the second intersection point of line `PS`
with the incircle. -/
noncomputable def t2 (p b c : ℝ) : ℝ := s p b c * (s p b c - p) / dPS2 p b c

/-- `Q`: the intersection point of `PS` with the incircle that is nearer to `P`. -/
noncomputable def Qp (p b c : ℝ) : Plane :=
  Pp p b c + t1 p b c • (Sp p b c - Pp p b c)

/-- `Q₂`: the second intersection point of `PS` with the incircle. -/
noncomputable def Q2p (p b c : ℝ) : Plane :=
  Pp p b c + t2 p b c • (Sp p b c - Pp p b c)

/-- `R`: the intersection of `BW` with `PS`. -/
noncomputable def Rp (p b c : ℝ) : Plane :=
  Pp p b c + (p / s p b c) • (Sp p b c - Pp p b c)

variable {p b c : ℝ} (hp : 0 < p) (hb : 0 < b) (hc : 0 < c)
  (hbc : p < b + c) (hpc : b < p + c) (hpb : c < p + b)

snip begin

include hp hb hc in
lemma s_pos : 0 < s p b c := by
  simp only [s]
  linarith

include hp hb hc in
lemma s_ne : s p b c ≠ 0 := (s_pos hp hb hc).ne'

include hbc in
lemma s_sub_p_pos : 0 < s p b c - p := by
  simp only [s]
  linarith

include hpb in
lemma s_sub_c_pos : 0 < s p b c - c := by
  simp only [s]
  linarith

include hp hb hc hbc hpc hpb in
lemma py_sq_pos : 0 < c ^ 2 - (px p b c) ^ 2 := by
  have hp2 : (0 : ℝ) < 4 * p ^ 2 := by positivity
  rw [← mul_pos_iff_of_pos_left hp2,
    show 4 * p ^ 2 * (c ^ 2 - (px p b c) ^ 2)
        = 4 * p ^ 2 * c ^ 2 - (2 * p * px p b c) ^ 2 by ring,
    show 2 * p * px p b c = c ^ 2 + p ^ 2 - b ^ 2 by
      simp only [px]
      field_simp [hp.ne'],
    show 4 * p ^ 2 * c ^ 2 - (c ^ 2 + p ^ 2 - b ^ 2) ^ 2
        = (b - c + p) * (b + c - p) * (c + p - b) * (c + p + b) by ring]
  have f1 : 0 < b - c + p := by linarith
  have f2 : 0 < b + c - p := by linarith
  have f3 : 0 < c + p - b := by linarith
  have f4 : 0 < c + p + b := by linarith
  positivity

include hp hb hc hbc hpc hpb in
lemma py_sq : (py p b c) ^ 2 = c ^ 2 - (px p b c) ^ 2 :=
  Real.sq_sqrt (py_sq_pos hp hb hc hbc hpc hpb).le

include hp hb hc hbc hpc hpb in
lemma py_pos : 0 < py p b c :=
  Real.sqrt_pos.mpr (py_sq_pos hp hb hc hbc hpc hpb)

include hp hb hc hbc hpc hpb in
lemma dps2_pos : 0 < dPS2 p b c := by
  simp only [dPS2]
  exact add_pos_of_nonneg_of_pos (sq_nonneg _) (pow_pos (py_pos hp hb hc hbc hpc hpb) 2)

include hp hb hc hbc hpc hpb in
lemma dps2_ne : dPS2 p b c ≠ 0 := (dps2_pos hp hb hc hbc hpc hpb).ne'

/-- Squared distance between two points of the plane, coordinatewise. -/
lemma dist_sq (x y : Plane) :
    (dist x y) ^ 2 = (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_two]
  simp only [Real.dist_eq, sq_abs]
  rw [Real.sq_sqrt (by positivity)]

include hp hb hc hbc hpc hpb in
lemma dist_P_B : dist (Pp p b c) Bp = c := by
  have h : (dist (Pp p b c) Bp) ^ 2 = c ^ 2 := by
    rw [dist_sq]
    simp only [Pp, Bp, Matrix.cons_val_zero, Matrix.cons_val_one, sub_zero]
    rw [py_sq hp hb hc hbc hpc hpb]
    ring
  exact (sq_eq_sq₀ dist_nonneg hc.le).mp h

include hp hb hc hbc hpc hpb in
lemma dist_P_C : dist (Pp p b c) (Cp p) = b := by
  have h : (dist (Pp p b c) (Cp p)) ^ 2 = b ^ 2 := by
    rw [dist_sq]
    simp only [Pp, Cp, Matrix.cons_val_zero, Matrix.cons_val_one, sub_zero]
    rw [py_sq hp hb hc hbc hpc hpb]
    simp only [px]
    field_simp [hp.ne']
    ring
  exact (sq_eq_sq₀ dist_nonneg hb.le).mp h

lemma dist_P_S_sq : (dist (Pp p b c) (Sp p b c)) ^ 2 = dPS2 p b c := by
  rw [dist_sq]
  simp only [Pp, Sp, dPS2, Matrix.cons_val_zero, Matrix.cons_val_one, sub_zero]
  ring

include hp hb hc hbc hpc hpb in
lemma dist_P_S_pos : 0 < dist (Pp p b c) (Sp p b c) := by
  have h2 := dps2_pos hp hb hc hbc hpc hpb
  rw [← dist_P_S_sq] at h2
  by_contra h
  push Not at h
  have h0 : dist (Pp p b c) (Sp p b c) = 0 := le_antisymm h dist_nonneg
  rw [h0] at h2
  simp at h2

include hp hb hc hbc in
lemma t1_pos : 0 < t1 p b c := div_pos (s_sub_p_pos hbc) (s_pos hp hb hc)

include hp hb hc hbc hpc hpb in
lemma t2_pos : 0 < t2 p b c :=
  div_pos (mul_pos (s_pos hp hb hc) (s_sub_p_pos hbc)) (dps2_pos hp hb hc hbc hpc hpb)

include hp hb hc hbc hpc hpb in
lemma rad_pos : 0 < rad p b c :=
  div_pos (mul_pos hp (py_pos hp hb hc hbc hpc hpb)) (mul_pos (by norm_num) (s_pos hp hb hc))

include hp hb hc hbc hpc hpb in
/-- The key algebraic identity: the squared distance from a point of the
line `PS` (parametrized by `t`) to the incenter, minus `r²`, factors as
`(t - t₁) * (|PS|² * t - s * (s - p))`. -/
lemma key_identity (t : ℝ) :
    (dist (Pp p b c + t • (Sp p b c - Pp p b c)) (Ip p b c)) ^ 2
      = (rad p b c) ^ 2
        + (t - t1 p b c) * (dPS2 p b c * t - s p b c * (s p b c - p)) := by
  have hpbc : p + b + c ≠ 0 := by linarith
  rw [dist_sq]
  simp only [Pp, Sp, Ip, rad, t1, dPS2, s, px, PiLp.add_apply, PiLp.sub_apply,
    PiLp.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one]
  field_simp [hpbc, hp.ne']
  ring_nf
  rw [py_sq hp hb hc hbc hpc hpb]
  simp only [px]
  field_simp [hp.ne']
  ring

include hp hb hc hbc hpc hpb in
/-- `dPS2 * t₂ = s * (s - p)`: the defining relation of the second root. -/
lemma t2_prop : dPS2 p b c * t2 p b c = s p b c * (s p b c - p) := by
  simp only [t2]
  rw [← mul_div_assoc, mul_div_cancel_left₀ _ (dps2_ne hp hb hc hbc hpc hpb)]

include hp hb hc hbc hpc hpb in
/-- `Q` lies on the incircle. -/
lemma dist_Q_I : dist (Qp p b c) (Ip p b c) = rad p b c := by
  have hkey := key_identity hp hb hc hbc hpc hpb (t1 p b c)
  rw [sub_self, zero_mul, add_zero] at hkey
  exact (sq_eq_sq₀ dist_nonneg (rad_pos hp hb hc hbc hpc hpb).le).mp hkey

include hp hb hc hbc hpc hpb in
/-- `Q₂` lies on the incircle. -/
lemma dist_Q2_I : dist (Q2p p b c) (Ip p b c) = rad p b c := by
  have hkey := key_identity hp hb hc hbc hpc hpb (t2 p b c)
  rw [t2_prop hp hb hc hbc hpc hpb, sub_self, mul_zero, add_zero] at hkey
  exact (sq_eq_sq₀ dist_nonneg (rad_pos hp hb hc hbc hpc hpb).le).mp hkey

include hp hb hc hbc hpc hpb in
/-- The line `PS` meets the incircle in exactly the two points `Q` and `Q₂`. -/
lemma only_two_intersections (t : ℝ)
    (h : dist (Pp p b c + t • (Sp p b c - Pp p b c)) (Ip p b c) = rad p b c) :
    t = t1 p b c ∨ t = t2 p b c := by
  have hkey := key_identity hp hb hc hbc hpc hpb t
  rw [h] at hkey
  have h0 : (t - t1 p b c) * (dPS2 p b c * t - s p b c * (s p b c - p)) = 0 := by
    linarith
  rcases mul_eq_zero.mp h0 with h1 | h2
  · exact Or.inl (sub_eq_zero.mp h1)
  · have hd : dPS2 p b c * t = s p b c * (s p b c - p) := by linarith
    have hd' : t * dPS2 p b c = s p b c * (s p b c - p) := by
      rw [mul_comm]
      exact hd
    exact Or.inr ((eq_div_iff (dps2_ne hp hb hc hbc hpc hpb)).mpr hd')

include hp hb hc hbc hpc hpb in
/-- `|PS|² < s²`, which will imply that `Q` is nearer to `P` than `Q₂`. -/
lemma dps2_lt_s_sq : dPS2 p b c < (s p b c) ^ 2 := by
  have hkey : (s p b c) ^ 2 - dPS2 p b c = 2 * (s p b c - c) * (c + px p b c) := by
    simp only [dPS2]
    rw [py_sq hp hb hc hbc hpc hpb]
    ring
  have hlt : -c < px p b c := by
    have h := py_sq_pos hp hb hc hbc hpc hpb
    by_contra hpx
    push Not at hpx
    have e1 : (0 : ℝ) ≤ c - px p b c := by linarith
    have e2 : c + px p b c ≤ 0 := by linarith
    have e3 : (c - px p b c) * (c + px p b c) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos e1 e2
    have e4 : (c - px p b c) * (c + px p b c) = c ^ 2 - (px p b c) ^ 2 := by ring
    linarith
  have h1 : 0 < c + px p b c := by linarith
  have h2 : 0 < 2 * (s p b c - c) * (c + px p b c) :=
    mul_pos (mul_pos (by norm_num) (s_sub_c_pos hpb)) h1
  linarith

include hp hb hc hbc hpc hpb in
lemma t1_lt_t2 : t1 p b c < t2 p b c := by
  simp only [t1, t2]
  rw [div_lt_div_iff₀ (s_pos hp hb hc) (dps2_pos hp hb hc hbc hpc hpb)]
  have hD : dPS2 p b c < (s p b c) ^ 2 := dps2_lt_s_sq hp hb hc hbc hpc hpb
  have hsp : 0 < s p b c - p := s_sub_p_pos hbc
  calc (s p b c - p) * dPS2 p b c
      < (s p b c - p) * (s p b c * s p b c) := by
        rw [mul_lt_mul_iff_right₀ hsp, ← pow_two]
        exact hD
    _ = s p b c * (s p b c - p) * s p b c := by ring

include hp hb hc hbc in
/-- `dist P Q = t₁ * dist P S`. -/
lemma dist_P_Q : dist (Pp p b c) (Qp p b c) = t1 p b c * dist (Pp p b c) (Sp p b c) := by
  rw [dist_comm (Pp p b c) (Qp p b c), dist_eq_norm]
  have h1 : Qp p b c - Pp p b c = t1 p b c • (Sp p b c - Pp p b c) := by
    simp only [Qp]
    abel
  rw [h1, norm_smul, Real.norm_eq_abs, abs_of_pos (t1_pos hp hb hc hbc), ← dist_eq_norm,
    dist_comm (Sp p b c) (Pp p b c)]

include hp hb hc hbc hpc hpb in
/-- `dist P Q₂ = t₂ * dist P S`. -/
lemma dist_P_Q2 : dist (Pp p b c) (Q2p p b c) = t2 p b c * dist (Pp p b c) (Sp p b c) := by
  rw [dist_comm (Pp p b c) (Q2p p b c), dist_eq_norm]
  have h1 : Q2p p b c - Pp p b c = t2 p b c • (Sp p b c - Pp p b c) := by
    simp only [Q2p]
    abel
  rw [h1, norm_smul, Real.norm_eq_abs, abs_of_pos (t2_pos hp hb hc hbc hpc hpb),
    ← dist_eq_norm, dist_comm (Sp p b c) (Pp p b c)]

include hp hb hc in
/-- `R` lies on the line `BW` (recall `B` is the origin). -/
lemma R_on_BW : Rp p b c = (b / s p b c) • Wp p b c := by
  have hpbc : p + b + c ≠ 0 := by linarith
  have h0 : Rp p b c 0 = ((b / s p b c) • Wp p b c) 0 := by
    simp only [Rp, Wp, Pp, Cp, Sp, s, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
      smul_eq_mul, Matrix.cons_val_zero]
    field_simp [hpbc, hb.ne']
    ring
  have h1 : Rp p b c 1 = ((b / s p b c) • Wp p b c) 1 := by
    simp only [Rp, Wp, Pp, Cp, Sp, s, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
      smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one]
    field_simp [hpbc, hb.ne']
    ring
  ext i
  fin_cases i
  · exact h0
  · exact h1

include hp hb hc hbc in
/-- `dist R S = ((s - p)/s) * dist P S`. -/
lemma dist_R_S : dist (Rp p b c) (Sp p b c)
    = ((s p b c - p) / s p b c) * dist (Pp p b c) (Sp p b c) := by
  have hpos : 0 < 1 - p / s p b c := by
    rw [sub_pos, div_lt_one (s_pos hp hb hc)]
    linarith [s_sub_p_pos hbc]
  have hcoef : 1 - p / s p b c = (s p b c - p) / s p b c := by
    field_simp [s_ne hp hb hc]
  rw [dist_comm (Rp p b c) (Sp p b c), dist_eq_norm]
  have h1 : Sp p b c - Rp p b c
      = (1 - p / s p b c) • (Sp p b c - Pp p b c) := by
    rw [Rp, sub_smul, one_smul]
    abel
  rw [h1, norm_smul, Real.norm_eq_abs, abs_of_pos hpos, ← dist_eq_norm,
    dist_comm (Sp p b c) (Pp p b c), hcoef]

include hpb in
/-- `BS = s - c`. -/
lemma dist_B_S : dist Bp (Sp p b c) = s p b c - c := by
  have h : (dist Bp (Sp p b c)) ^ 2 = (s p b c - c) ^ 2 := by
    rw [dist_sq]
    simp only [Bp, Sp, Matrix.cons_val_zero, Matrix.cons_val_one, sub_zero]
    ring
  exact (sq_eq_sq₀ dist_nonneg (s_sub_c_pos hpb).le).mp h

include hpb in
/-- `CU = s - c`. -/
lemma dist_C_U : dist (Cp p) (Up p b c) = s p b c - c := by
  have h : (dist (Cp p) (Up p b c)) ^ 2 = (s p b c - c) ^ 2 := by
    rw [dist_sq]
    simp only [Cp, Up, s, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  exact (sq_eq_sq₀ dist_nonneg (s_sub_c_pos hpb).le).mp h

include hpb in
/-- The defining property of `S`: `BS = CU`. -/
lemma BS_eq_CU : dist Bp (Sp p b c) = dist (Cp p) (Up p b c) := by
  rw [dist_B_S hpb, dist_C_U hpb]

include hp hb hc hbc hpc hpb in
/-- `U` lies on the incircle (it is the touchpoint on `BC`). -/
lemma dist_U_I : dist (Up p b c) (Ip p b c) = rad p b c := by
  have h : (dist (Up p b c) (Ip p b c)) ^ 2 = (rad p b c) ^ 2 := by
    rw [dist_sq]
    simp only [Up, Ip, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  exact (sq_eq_sq₀ dist_nonneg (rad_pos hp hb hc hbc hpc hpb).le).mp h

include hp hb hc hbc hpc hpb in
/-- `PW = s - c`: the point `W` satisfies `PW = CV`. -/
lemma dist_P_W : dist (Pp p b c) (Wp p b c) = s p b c - c := by
  rw [dist_comm (Pp p b c) (Wp p b c), dist_eq_norm]
  have h1 : Wp p b c - Pp p b c = ((s p b c - c) / b) • (Cp p - Pp p b c) := by
    simp only [Wp]
    abel
  rw [h1, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos (s_sub_c_pos hpb) hb),
    ← dist_eq_norm, dist_comm (Cp p) (Pp p b c), dist_P_C hp hb hc hbc hpc hpb]
  exact div_mul_cancel₀ _ hb.ne'

include hp hb hc hbc hpc hpb in
/-- `CV = s - c`. -/
lemma dist_C_V : dist (Cp p) (Vp p b c) = s p b c - c := by
  rw [dist_comm (Cp p) (Vp p b c), dist_eq_norm]
  have h1 : Vp p b c - Cp p = ((s p b c - c) / b) • (Pp p b c - Cp p) := by
    simp only [Vp]
    abel
  rw [h1, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos (s_sub_c_pos hpb) hb),
    ← dist_eq_norm, dist_P_C hp hb hc hbc hpc hpb]
  exact div_mul_cancel₀ _ hb.ne'

include hp hb hc hbc hpc hpb in
/-- `V` lies on the incircle. -/
lemma dist_V_I : dist (Vp p b c) (Ip p b c) = rad p b c := by
  have hpbc : p + b + c ≠ 0 := by linarith
  have h : (dist (Vp p b c) (Ip p b c)) ^ 2 = (rad p b c) ^ 2 := by
    rw [dist_sq]
    simp only [Vp, Ip, Pp, Cp, rad, s, px, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
      smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one]
    field_simp [hpbc, hb.ne', hp.ne']
    ring_nf
    rw [py_sq hp hb hc hbc hpc hpb]
    simp only [px]
    field_simp [hp.ne']
    ring
  exact (sq_eq_sq₀ dist_nonneg (rad_pos hp hb hc hbc hpc hpb).le).mp h

include hp hb hc hbc hpc hpb in
/-- `IV` is perpendicular to `PC`, so the incircle indeed touches `PC` at `V`. -/
lemma V_perp : (Vp p b c 0 - Ip p b c 0) * (Pp p b c 0 - Cp p 0)
    + (Vp p b c 1 - Ip p b c 1) * (Pp p b c 1 - Cp p 1) = 0 := by
  have hpbc : p + b + c ≠ 0 := by linarith
  simp only [Vp, Ip, Pp, Cp, rad, s, px, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
    smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one]
  field_simp [hpbc, hb.ne', hp.ne']
  ring_nf
  rw [py_sq hp hb hc hbc hpc hpb]
  simp only [px]
  field_simp [hp.ne']
  ring

snip end

problem usa2001_p2 (p b c : ℝ) (hp : 0 < p) (hb : 0 < b) (hc : 0 < c)
    (hbc : p < b + c) (hpc : b < p + c) (hpb : c < p + b) :
    -- `Q` lies on the incircle
    dist (Qp p b c) (Ip p b c) = rad p b c ∧
    -- `Q₂` lies on the incircle
    dist (Q2p p b c) (Ip p b c) = rad p b c ∧
    -- the line `PS` meets the incircle in exactly these two points
    (∀ t : ℝ, dist (Pp p b c + t • (Sp p b c - Pp p b c)) (Ip p b c) = rad p b c →
      t = t1 p b c ∨ t = t2 p b c) ∧
    -- `Q` is the intersection point nearer to `P`
    dist (Pp p b c) (Qp p b c) < dist (Pp p b c) (Q2p p b c) ∧
    -- `R` lies on the line `BW`
    Rp p b c = (b / s p b c) • Wp p b c ∧
    -- the conclusion: `PQ = RS`
    dist (Pp p b c) (Qp p b c) = dist (Rp p b c) (Sp p b c) := by
  refine ⟨dist_Q_I hp hb hc hbc hpc hpb, dist_Q2_I hp hb hc hbc hpc hpb,
    fun t ht => only_two_intersections hp hb hc hbc hpc hpb t ht, ?_,
    R_on_BW hp hb hc, ?_⟩
  · rw [dist_P_Q hp hb hc hbc, dist_P_Q2 hp hb hc hbc hpc hpb]
    exact mul_lt_mul_of_pos_right (t1_lt_t2 hp hb hc hbc hpc hpb)
      (dist_P_S_pos hp hb hc hbc hpc hpb)
  · rw [dist_P_Q hp hb hc hbc, dist_R_S hp hb hc hbc]
    simp only [t1]

end Usa2001P2
