/-
Copyright (c) 2026 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw, Kimi K3
-/

module

public import Mathlib.Tactic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Olympiad 1993, Problem 4

For three points P, Q, R in the plane define m(PQR) as the minimum length
of the three altitudes of the triangle PQR (or zero if the points are
collinear). Prove that for any points A, B, C, X:

    m(ABC) ≤ m(ABX) + m(AXC) + m(XBC).
-/

namespace Imo1993P4

abbrev Pt := EuclideanSpace ℝ (Fin 2)

snip begin

/-!
### Definitions

We work with coordinate algebra on `EuclideanSpace ℝ (Fin 2)`.
The key observation is that the minimum altitude of a triangle equals twice
its area divided by its longest side, so we *define* `m` by that formula
(with the convention that it is `0` for collinear points, which is automatic
since then the area vanishes; for three coinciding points Lean's division
gives `0/0 = 0`).
-/

/-- The scalar 2D cross product. -/
def cross (x y : Pt) : ℝ := x 0 * y 1 - x 1 * y 0

/-- The scalar 2D dot product. -/
def dot (x y : Pt) : ℝ := x 0 * y 0 + x 1 * y 1

/-- Rotation by 90 degrees. -/
def perp (x : Pt) : Pt := !₂[-x 1, x 0]

/-- The signed area of the triangle `PQR`. -/
noncomputable def sarea (P Q R : Pt) : ℝ := cross (Q - P) (R - P) / 2

/-- The length of the longest side of the triangle `PQR`. -/
noncomputable def sideMax (P Q R : Pt) : ℝ := max (dist P Q) (max (dist Q R) (dist R P))

/-- `m P Q R` is the minimum altitude of the triangle `PQR`, given by twice
the area over the longest side. -/
noncomputable def m (P Q R : Pt) : ℝ := 2 * |sarea P Q R| / sideMax P Q R

/-! ### Basic extensionality and coordinate lemmas -/

lemma Pt_ext {x y : Pt} (h : ∀ i, x i = y i) : x = y := by
  apply WithLp.ofLp_injective (p := 2)
  funext i
  exact h i

lemma norm_sq (x : Pt) : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.norm_eq_abs, Real.norm_eq_abs,
    sq_abs, sq_abs]
  exact Real.sq_sqrt (by positivity)

lemma dist_sq (P Q : Pt) : dist P Q ^ 2 = (P 0 - Q 0) ^ 2 + (P 1 - Q 1) ^ 2 := by
  rw [dist_eq_norm, norm_sq, PiLp.sub_apply, PiLp.sub_apply]

/-! ### Algebra of `cross`, `dot`, `perp` -/

lemma dot_sub_left (x y v : Pt) : dot (x - y) v = dot x v - dot y v := by
  simp [dot, PiLp.sub_apply]; ring

lemma dot_add_left (x y v : Pt) : dot (x + y) v = dot x v + dot y v := by
  simp [dot, PiLp.add_apply]; ring

lemma dot_smul_left (c : ℝ) (x v : Pt) : dot (c • x) v = c * dot x v := by
  simp [dot, PiLp.smul_apply, smul_eq_mul]; ring

lemma dot_smul_right (c : ℝ) (x y : Pt) : dot x (c • y) = c * dot x y := by
  simp [dot, PiLp.smul_apply, smul_eq_mul]; ring

lemma perp_apply₀ (x : Pt) : perp x 0 = -x 1 := by
  simp [perp, PiLp.toLp_apply, Matrix.cons_val_zero]

lemma perp_apply₁ (x : Pt) : perp x 1 = x 0 := by
  simp [perp, PiLp.toLp_apply, Matrix.cons_val_one]

lemma perp_dot (x : Pt) : dot x (perp x) = 0 := by
  simp [dot, perp_apply₀, perp_apply₁]; ring

lemma dot_perp_left (x y : Pt) : dot (perp x) y = cross x y := by
  simp [dot, cross, perp_apply₀, perp_apply₁]; ring

lemma dot_perp_right (x y : Pt) : dot x (perp y) = -cross x y := by
  simp [dot, cross, perp_apply₀, perp_apply₁]; ring

lemma norm_perp (x : Pt) : ‖perp x‖ = ‖x‖ := by
  have h : ‖perp x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [norm_sq, norm_sq, perp_apply₀, perp_apply₁]; ring
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with h' | h'
  · exact h'
  · linarith [norm_nonneg (perp x), norm_nonneg x]

lemma cross_self (x : Pt) : cross x x = 0 := by simp [cross]; ring

lemma cross_add_right (x y z : Pt) : cross x (y + z) = cross x y + cross x z := by
  simp [cross, PiLp.add_apply]; ring

/-- Cauchy-Schwarz for the coordinate dot product. -/
lemma abs_dot_le (x y : Pt) : |dot x y| ≤ ‖x‖ * ‖y‖ := by
  apply abs_le_of_sq_le_sq _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  rw [mul_pow, norm_sq, norm_sq, dot]
  nlinarith [sq_nonneg (x 0 * y 1 - x 1 * y 0)]

/-- Expressing the cross product in an orthonormal basis `{u, perp u}`. -/
lemma cross_eq_dot (x y u : Pt) (hu : u 0 ^ 2 + u 1 ^ 2 = 1) :
    cross x y = dot x u * dot y (perp u) - dot x (perp u) * dot y u := by
  simp only [cross, dot, perp_apply₀, perp_apply₁]
  linear_combination (-(x 0 * y 1 - x 1 * y 0)) * hu

/-! ### Symmetries of `sarea`, `sideMax`, `m` -/

lemma sarea_self_left (P Q : Pt) : sarea P P Q = 0 := by
  simp [sarea, cross, PiLp.sub_apply]

lemma sarea_self_right (P Q : Pt) : sarea P Q Q = 0 := by
  simp [sarea, cross, PiLp.sub_apply]; ring

lemma sarea_swap21 (P Q R : Pt) : sarea Q P R = -sarea P Q R := by
  simp [sarea, cross, PiLp.sub_apply]; ring

lemma sarea_swap32 (P Q R : Pt) : sarea P R Q = -sarea P Q R := by
  simp [sarea, cross, PiLp.sub_apply]; ring

lemma sarea_rot (P Q R : Pt) : sarea Q R P = sarea P Q R := by
  simp [sarea, cross, PiLp.sub_apply]; ring

/-- The signed-area identity behind the area addition: for any four points,
`sarea A B C = sarea X B C + sarea A X C + sarea A B X`. -/
lemma sarea_id (A B C X : Pt) :
    sarea A B C = sarea X B C + sarea A X C + sarea A B X := by
  simp [sarea, cross, PiLp.sub_apply]; ring

lemma sideMax_swap21 (P Q R : Pt) : sideMax Q P R = sideMax P Q R := by
  simp [sideMax, dist_comm, max_comm]

lemma sideMax_swap32 (P Q R : Pt) : sideMax P R Q = sideMax P Q R := by
  simp [sideMax, dist_comm, max_comm, max_left_comm]

lemma sideMax_rot (P Q R : Pt) : sideMax Q R P = sideMax P Q R := by
  simp [sideMax, dist_comm, max_comm, max_left_comm]

lemma sideMax_nonneg (P Q R : Pt) : 0 ≤ sideMax P Q R :=
  le_trans dist_nonneg (le_max_left _ _)

lemma sideMax_eq_zero {P Q R : Pt} (h : sideMax P Q R = 0) : P = Q ∧ Q = R := by
  have hPQ : dist P Q ≤ 0 := le_trans (le_max_left _ _) (le_of_eq h)
  have hQR : dist Q R ≤ 0 :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_of_eq h)
  exact ⟨dist_eq_zero.mp (le_antisymm hPQ dist_nonneg),
    dist_eq_zero.mp (le_antisymm hQR dist_nonneg)⟩

lemma m_swap21 (P Q R : Pt) : m Q P R = m P Q R := by
  unfold m
  rw [sarea_swap21, abs_neg, sideMax_swap21]

lemma m_swap32 (P Q R : Pt) : m P R Q = m P Q R := by
  unfold m
  rw [sarea_swap32, abs_neg, sideMax_swap32]

lemma m_rot (P Q R : Pt) : m Q R P = m P Q R := by
  unfold m
  rw [sarea_rot, sideMax_rot]

lemma m_nonneg (P Q R : Pt) : 0 ≤ m P Q R :=
  div_nonneg (mul_nonneg (by norm_num) (abs_nonneg _)) (sideMax_nonneg _ _ _)

lemma m_eq_zero_of_sarea_eq_zero {P Q R : Pt} (h : sarea P Q R = 0) : m P Q R = 0 := by
  simp [m, h]

/-! ### Barycentric coordinates -/

/-- Cramer's rule: the barycentric coordinates of `X` with respect to the
nondegenerate triangle `ABC` are the signed-area ratios. -/
lemma bary_coords {A B C X : Pt} (_hs : sarea A B C ≠ 0) (i : Fin 2) :
    sarea A B C * X i =
      sarea X B C * A i + sarea A X C * B i + sarea A B X * C i := by
  fin_cases i <;> simp [sarea, cross, PiLp.sub_apply] <;> ring

/-- A convex combination of three points is within distance
`max (dist P A) (max (dist P B) (dist P C))` of any point `P`. -/
lemma dist_le_of_bary {P A B C X : Pt} {l₁ l₂ l₃ : ℝ}
    (h₁ : 0 ≤ l₁) (h₂ : 0 ≤ l₂) (h₃ : 0 ≤ l₃) (hsum : l₁ + l₂ + l₃ = 1)
    (hX : ∀ i, X i = l₁ * A i + l₂ * B i + l₃ * C i) :
    dist P X ≤ max (dist P A) (max (dist P B) (dist P C)) := by
  have hvec : P - X = l₁ • (P - A) + l₂ • (P - B) + l₃ • (P - C) := by
    apply Pt_ext
    intro i
    simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    rw [hX i]
    linear_combination -(P i) * hsum
  have hPA : ‖P - A‖ ≤ max (dist P A) (max (dist P B) (dist P C)) := by
    rw [← dist_eq_norm]; exact le_max_left _ _
  have hPB : ‖P - B‖ ≤ max (dist P A) (max (dist P B) (dist P C)) := by
    rw [← dist_eq_norm]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hPC : ‖P - C‖ ≤ max (dist P A) (max (dist P B) (dist P C)) := by
    rw [← dist_eq_norm]; exact le_trans (le_max_right _ _) (le_max_right _ _)
  calc dist P X = ‖P - X‖ := dist_eq_norm _ _
    _ = ‖l₁ • (P - A) + l₂ • (P - B) + l₃ • (P - C)‖ := by rw [hvec]
    _ ≤ ‖l₁ • (P - A)‖ + ‖l₂ • (P - B)‖ + ‖l₃ • (P - C)‖ :=
        le_trans (norm_add_le _ _) (add_le_add_left (norm_add_le _ _) _)
    _ = l₁ * ‖P - A‖ + l₂ * ‖P - B‖ + l₃ * ‖P - C‖ := by
        rw [norm_smul, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          Real.norm_eq_abs, abs_of_nonneg h₁, abs_of_nonneg h₂, abs_of_nonneg h₃]
    _ ≤ l₁ * max (dist P A) (max (dist P B) (dist P C)) +
        l₂ * max (dist P A) (max (dist P B) (dist P C)) +
        l₃ * max (dist P A) (max (dist P B) (dist P C)) := by
        gcongr
    _ = max (dist P A) (max (dist P B) (dist P C)) := by
        rw [← add_mul, ← add_mul, hsum, one_mul]

/-! ### The width bound

The key geometric fact: for any unit vector `u`, the width of the triangle
`PQR` in direction `u` (the maximal gap between the projections of the three
vertices onto `u`) is at least `m P Q R`. -/

/-- Auxiliary min/max identity used in the width bound. -/
lemma minmax_id (p q : ℝ) :
    min (min (|p| + |q|) (|p| + |p - q|)) (|q| + |p - q|) =
      max |p| (max |q| |p - q|) := by
  rcases abs_cases p with ⟨hp, hp'⟩ | ⟨hp, hp'⟩ <;>
  rcases abs_cases q with ⟨hq, hq'⟩ | ⟨hq, hq'⟩ <;>
  rcases abs_cases (p - q) with ⟨hpq, hpq'⟩ | ⟨hpq, hpq'⟩ <;>
  simp only [hp, hq, hpq, min_def, max_def] <;> split_ifs <;> linarith

lemma m_le_width (P Q R u : Pt) (hu : ‖u‖ = 1) :
    m P Q R ≤ max |dot (Q - P) u| (max |dot (R - P) u| |dot (R - Q) u|) := by
  have hu2 : u 0 ^ 2 + u 1 ^ 2 = 1 := by
    have h := norm_sq u
    rw [hu, one_pow] at h
    exact h.symm
  have hnorm_perp : ‖perp u‖ = 1 := by rw [norm_perp, hu]
  -- shorthand for the projections onto `u` and `perp u`
  set α := dot (Q - P) u with hα
  set β := dot (R - P) u with hβ
  set σ := dot (Q - P) (perp u) with hσ
  set ρ := dot (R - P) (perp u) with hρ
  set W := max |α| (max |β| |α - β|) with hW
  have hW0 : 0 ≤ W := le_trans (abs_nonneg α) (le_max_left _ _)
  have hαW : |α| ≤ W := le_max_left _ _
  have hβW : |β| ≤ W := le_trans (le_max_left _ _) (le_max_right _ _)
  have hαβW : |α - β| ≤ W := le_trans (le_max_right _ _) (le_max_right _ _)
  have hcross : cross (Q - P) (R - P) = α * ρ - σ * β := cross_eq_dot _ _ _ hu2
  -- the width of `PQR` in direction `u` is `W`
  have e2 : dot (R - Q) u = β - α := by
    have k := dot_sub_left (R - P) (Q - P) u
    rw [sub_sub_sub_cancel_right] at k
    exact k
  rw [e2, abs_sub_comm β α]
  -- three splittings of `α * ρ - σ * β`, giving `|cross| ≤ W * (sum of perp-gaps)`
  have hspl1 : α * ρ - σ * β = α * (ρ - σ) + σ * (α - β) := by ring
  have hspl2 : α * ρ - σ * β = β * (ρ - σ) + ρ * (α - β) := by ring
  have hb1 : |cross (Q - P) (R - P)| ≤ W * (|σ| + |σ - ρ|) := by
    rw [hcross, hspl1, ← abs_sub_comm ρ σ]
    calc |α * (ρ - σ) + σ * (α - β)|
        ≤ |α| * |ρ - σ| + |σ| * |α - β| := by
            rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ W * |ρ - σ| + |σ| * W :=
            add_le_add (mul_le_mul_of_nonneg_right hαW (abs_nonneg _))
              (mul_le_mul_of_nonneg_left hαβW (abs_nonneg _))
      _ = W * (|σ| + |ρ - σ|) := by ring
  have hb2 : |cross (Q - P) (R - P)| ≤ W * (|ρ| + |σ - ρ|) := by
    rw [hcross, hspl2, ← abs_sub_comm ρ σ]
    calc |β * (ρ - σ) + ρ * (α - β)|
        ≤ |β| * |ρ - σ| + |ρ| * |α - β| := by
            rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ W * |ρ - σ| + |ρ| * W :=
            add_le_add (mul_le_mul_of_nonneg_right hβW (abs_nonneg _))
              (mul_le_mul_of_nonneg_left hαβW (abs_nonneg _))
      _ = W * (|ρ| + |ρ - σ|) := by ring
  have hb3 : |cross (Q - P) (R - P)| ≤ W * (|σ| + |ρ|) := by
    rw [hcross]
    calc |α * ρ - σ * β|
        ≤ |α| * |ρ| + |σ| * |β| := by
            have h := abs_add_le (α * ρ) (-(σ * β))
            rw [abs_neg, abs_mul, abs_mul] at h
            rwa [sub_eq_add_neg]
      _ ≤ W * |ρ| + |σ| * W :=
            add_le_add (mul_le_mul_of_nonneg_right hαW (abs_nonneg _))
              (mul_le_mul_of_nonneg_left hβW (abs_nonneg _))
      _ = W * (|σ| + |ρ|) := by ring
  -- combining: `|cross| ≤ W * N` where `N` is the width in direction `perp u`
  have hN : |cross (Q - P) (R - P)| ≤ W * max |σ| (max |ρ| |σ - ρ|) := by
    rw [← minmax_id σ ρ, mul_min_of_nonneg _ _ hW0, mul_min_of_nonneg _ _ hW0,
      le_min_iff, le_min_iff]
    exact ⟨⟨hb3, hb1⟩, hb2⟩
  -- the width in direction `perp u` is at most the longest side
  have hσS : |σ| ≤ sideMax P Q R := by
    have h1 := abs_dot_le (Q - P) (perp u)
    rw [hnorm_perp, mul_one] at h1
    have e : ‖Q - P‖ = dist P Q := by rw [← dist_eq_norm, dist_comm]
    rw [e] at h1
    exact le_trans h1 (le_max_left _ _)
  have hρS : |ρ| ≤ sideMax P Q R := by
    have h1 := abs_dot_le (R - P) (perp u)
    rw [hnorm_perp, mul_one] at h1
    have e : ‖R - P‖ = dist R P := by rw [← dist_eq_norm]
    rw [e] at h1
    exact le_trans h1 (le_trans (le_max_right _ _) (le_max_right _ _))
  have hσρS : |σ - ρ| ≤ sideMax P Q R := by
    have e : σ - ρ = dot (Q - R) (perp u) := by
      have k := dot_sub_left (Q - P) (R - P) (perp u)
      rw [sub_sub_sub_cancel_right] at k
      exact k.symm
    rw [e]
    have h1 := abs_dot_le (Q - R) (perp u)
    rw [hnorm_perp, mul_one] at h1
    have e2' : ‖Q - R‖ = dist Q R := by rw [← dist_eq_norm]
    rw [e2'] at h1
    exact le_trans h1 (le_trans (le_max_left _ _) (le_max_right _ _))
  have hNle : max |σ| (max |ρ| |σ - ρ|) ≤ sideMax P Q R := by
    rw [max_le_iff, max_le_iff]
    exact ⟨hσS, hρS, hσρS⟩
  -- conclude
  have hm : m P Q R = |cross (Q - P) (R - P)| / sideMax P Q R := by
    unfold m sarea
    rw [abs_div, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    ring
  by_cases hS : sideMax P Q R = 0
  · rw [hm, hS, div_zero]
    exact hW0
  · have hSpos : 0 < sideMax P Q R := lt_of_le_of_ne (sideMax_nonneg _ _ _) (Ne.symm hS)
    rw [hm, div_le_iff₀ hSpos]
    exact le_trans hN (mul_le_mul_of_nonneg_left hNle hW0)

/-! ### Monotonicity of `m` under triangle inclusion -/

lemma m_mono_aux {P Q R P' Q' R' : Pt} {a₁ a₂ a₃ b₁ b₂ b₃ c₁ c₂ c₃ : ℝ}
    (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (ha₃ : 0 ≤ a₃) (ha : a₁ + a₂ + a₃ = 1)
    (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) (hb₃ : 0 ≤ b₃) (hb : b₁ + b₂ + b₃ = 1)
    (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hc₃ : 0 ≤ c₃) (hc : c₁ + c₂ + c₃ = 1)
    (hP : ∀ i, P i = a₁ * P' i + a₂ * Q' i + a₃ * R' i)
    (hQ : ∀ i, Q i = b₁ * P' i + b₂ * Q' i + b₃ * R' i)
    (hR : ∀ i, R i = c₁ * P' i + c₂ * Q' i + c₃ * R' i)
    (hmax : sideMax P' Q' R' = dist Q' R') (hne : dist Q' R' ≠ 0) :
    m P Q R ≤ m P' Q' R' := by
  -- the unit vector perpendicular to the longest side `Q'R'`
  have hQR : ‖R' - Q'‖ ≠ 0 := by
    have e : ‖Q' - R'‖ = ‖R' - Q'‖ := by rw [← norm_neg (Q' - R'), neg_sub]
    rw [dist_eq_norm] at hne
    rw [← e]
    exact hne
  set u := (‖R' - Q'‖)⁻¹ • perp (R' - Q') with hu_def
  have hu : ‖u‖ = 1 := by
    rw [hu_def, norm_smul, norm_perp, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_mul_cancel₀ hQR]
  -- projections of the primed points onto `u`
  have d3 : dot (R' - Q') u = 0 := by
    rw [hu_def, dot_smul_right, perp_dot, mul_zero]
  have d2eq : dot (R' - P') u = dot (Q' - P') u := by
    rw [(sub_add_sub_cancel R' Q' P').symm, dot_add_left, d3, zero_add]
  -- twice the area of `P'Q'R'` equals `‖R' - Q'‖ * |dot (Q' - P') u|`
  have e1 : cross (Q' - P') (R' - P') = cross (Q' - P') (R' - Q') := by
    rw [(sub_add_sub_cancel R' Q' P').symm, cross_add_right, cross_self, add_zero]
  have e2 : cross (Q' - P') (R' - Q') = -dot (Q' - P') (perp (R' - Q')) := by
    rw [dot_perp_right, neg_neg]
  have e3 : dot (Q' - P') (perp (R' - Q')) = ‖R' - Q'‖ * dot (Q' - P') u := by
    rw [hu_def, dot_smul_right, ← mul_assoc, mul_inv_cancel₀ hQR, one_mul]
  have hcross : 2 * |sarea P' Q' R'| = ‖R' - Q'‖ * |dot (Q' - P') u| := by
    unfold sarea
    rw [e1, e2, e3, abs_div, abs_neg, abs_mul, abs_of_nonneg (norm_nonneg _),
      abs_of_pos (by norm_num : (0:ℝ) < 2)]
    ring
  -- hence `m P' Q' R'` equals the width of `P'Q'R'` in direction `u`
  have hm' : m P' Q' R' = |dot (Q' - P') u| := by
    unfold m
    rw [hmax, hcross, dist_eq_norm]
    have e : ‖Q' - R'‖ = ‖R' - Q'‖ := by rw [← norm_neg (Q' - R'), neg_sub]
    rw [e, mul_div_cancel_left₀ _ hQR]
  -- the projections of `P`, `Q`, `R` lie in the interval of the primed projections
  set dP := dot P' u with hdP
  set dQ := dot Q' u with hdQ
  set dR := dot R' u with hdR
  set lo := min dP (min dQ dR) with hlo_def
  set hi := max dP (max dQ dR) with hhi_def
  have hPdot : dot P u = a₁ * dP + a₂ * dQ + a₃ * dR := by
    simp only [dot, hdP, hdQ, hdR, hP 0, hP 1]; ring
  have hQdot : dot Q u = b₁ * dP + b₂ * dQ + b₃ * dR := by
    simp only [dot, hdP, hdQ, hdR, hQ 0, hQ 1]; ring
  have hRdot : dot R u = c₁ * dP + c₂ * dQ + c₃ * dR := by
    simp only [dot, hdP, hdQ, hdR, hR 0, hR 1]; ring
  have hlo1 : lo ≤ dP := min_le_left _ _
  have hlo2 : lo ≤ dQ := le_trans (min_le_right _ _) (min_le_left _ _)
  have hlo3 : lo ≤ dR := le_trans (min_le_right _ _) (min_le_right _ _)
  have hhi1 : dP ≤ hi := le_max_left _ _
  have hhi2 : dQ ≤ hi := le_trans (le_max_left _ _) (le_max_right _ _)
  have hhi3 : dR ≤ hi := le_trans (le_max_right _ _) (le_max_right _ _)
  have hPlo : lo ≤ dot P u := by
    rw [hPdot]
    have e : a₁ * dP + a₂ * dQ + a₃ * dR - lo =
        a₁ * (dP - lo) + a₂ * (dQ - lo) + a₃ * (dR - lo) := by
      linear_combination lo * ha
    have g1 : 0 ≤ a₁ * (dP - lo) := mul_nonneg ha₁ (sub_nonneg.mpr hlo1)
    have g2 : 0 ≤ a₂ * (dQ - lo) := mul_nonneg ha₂ (sub_nonneg.mpr hlo2)
    have g3 : 0 ≤ a₃ * (dR - lo) := mul_nonneg ha₃ (sub_nonneg.mpr hlo3)
    linarith [e, g1, g2, g3]
  have hPhi : dot P u ≤ hi := by
    rw [hPdot]
    have e : hi - (a₁ * dP + a₂ * dQ + a₃ * dR) =
        a₁ * (hi - dP) + a₂ * (hi - dQ) + a₃ * (hi - dR) := by
      linear_combination -hi * ha
    have g1 : 0 ≤ a₁ * (hi - dP) := mul_nonneg ha₁ (sub_nonneg.mpr hhi1)
    have g2 : 0 ≤ a₂ * (hi - dQ) := mul_nonneg ha₂ (sub_nonneg.mpr hhi2)
    have g3 : 0 ≤ a₃ * (hi - dR) := mul_nonneg ha₃ (sub_nonneg.mpr hhi3)
    linarith [e, g1, g2, g3]
  have hQlo : lo ≤ dot Q u := by
    rw [hQdot]
    have e : b₁ * dP + b₂ * dQ + b₃ * dR - lo =
        b₁ * (dP - lo) + b₂ * (dQ - lo) + b₃ * (dR - lo) := by
      linear_combination lo * hb
    have g1 : 0 ≤ b₁ * (dP - lo) := mul_nonneg hb₁ (sub_nonneg.mpr hlo1)
    have g2 : 0 ≤ b₂ * (dQ - lo) := mul_nonneg hb₂ (sub_nonneg.mpr hlo2)
    have g3 : 0 ≤ b₃ * (dR - lo) := mul_nonneg hb₃ (sub_nonneg.mpr hlo3)
    linarith [e, g1, g2, g3]
  have hQhi : dot Q u ≤ hi := by
    rw [hQdot]
    have e : hi - (b₁ * dP + b₂ * dQ + b₃ * dR) =
        b₁ * (hi - dP) + b₂ * (hi - dQ) + b₃ * (hi - dR) := by
      linear_combination -hi * hb
    have g1 : 0 ≤ b₁ * (hi - dP) := mul_nonneg hb₁ (sub_nonneg.mpr hhi1)
    have g2 : 0 ≤ b₂ * (hi - dQ) := mul_nonneg hb₂ (sub_nonneg.mpr hhi2)
    have g3 : 0 ≤ b₃ * (hi - dR) := mul_nonneg hb₃ (sub_nonneg.mpr hhi3)
    linarith [e, g1, g2, g3]
  have hRlo : lo ≤ dot R u := by
    rw [hRdot]
    have e : c₁ * dP + c₂ * dQ + c₃ * dR - lo =
        c₁ * (dP - lo) + c₂ * (dQ - lo) + c₃ * (dR - lo) := by
      linear_combination lo * hc
    have g1 : 0 ≤ c₁ * (dP - lo) := mul_nonneg hc₁ (sub_nonneg.mpr hlo1)
    have g2 : 0 ≤ c₂ * (dQ - lo) := mul_nonneg hc₂ (sub_nonneg.mpr hlo2)
    have g3 : 0 ≤ c₃ * (dR - lo) := mul_nonneg hc₃ (sub_nonneg.mpr hlo3)
    linarith [e, g1, g2, g3]
  have hRhi : dot R u ≤ hi := by
    rw [hRdot]
    have e : hi - (c₁ * dP + c₂ * dQ + c₃ * dR) =
        c₁ * (hi - dP) + c₂ * (hi - dQ) + c₃ * (hi - dR) := by
      linear_combination -hi * hc
    have g1 : 0 ≤ c₁ * (hi - dP) := mul_nonneg hc₁ (sub_nonneg.mpr hhi1)
    have g2 : 0 ≤ c₂ * (hi - dQ) := mul_nonneg hc₂ (sub_nonneg.mpr hhi2)
    have g3 : 0 ≤ c₃ * (hi - dR) := mul_nonneg hc₃ (sub_nonneg.mpr hhi3)
    linarith [e, g1, g2, g3]
  -- hence the width of `PQR` in direction `u` is at most `hi - lo`
  have g1 : |dot (Q - P) u| ≤ hi - lo := by
    rw [dot_sub_left]
    exact abs_le.mpr ⟨by linarith [hPhi, hQlo], by linarith [hPlo, hQhi]⟩
  have g2 : |dot (R - P) u| ≤ hi - lo := by
    rw [dot_sub_left]
    exact abs_le.mpr ⟨by linarith [hPhi, hRlo], by linarith [hPlo, hRhi]⟩
  have g3 : |dot (R - Q) u| ≤ hi - lo := by
    rw [dot_sub_left]
    exact abs_le.mpr ⟨by linarith [hQhi, hRlo], by linarith [hQlo, hRhi]⟩
  have hwidth : max |dot (Q - P) u| (max |dot (R - P) u| |dot (R - Q) u|) ≤ hi - lo := by
    rw [max_le_iff, max_le_iff]
    exact ⟨g1, g2, g3⟩
  -- and `hi - lo` equals the width of `P'Q'R'`
  have hdR : dR = dQ := by
    have k := dot_sub_left R' Q' u
    rw [d3] at k
    rw [hdR, hdQ]
    linarith [k]
  have hdQdP : dot (Q' - P') u = dQ - dP := by
    rw [hdQ, hdP]
    exact dot_sub_left Q' P' u
  have hhi : hi - lo = |dot (Q' - P') u| := by
    rw [hdQdP, hhi_def, hlo_def, hdR, max_self, min_self]
    rcases le_total dP dQ with h | h
    · rw [max_eq_right h, min_eq_left h, abs_of_nonneg (sub_nonneg.mpr h)]
    · rw [max_eq_left h, min_eq_right h, abs_of_nonpos (sub_nonpos.mpr h), neg_sub]
  -- chain the inequalities
  calc m P Q R ≤ max |dot (Q - P) u| (max |dot (R - P) u| |dot (R - Q) u|) :=
      m_le_width P Q R u hu
    _ ≤ hi - lo := hwidth
    _ = |dot (Q' - P') u| := hhi
    _ = m P' Q' R' := hm'.symm

lemma m_mono {P Q R P' Q' R' : Pt} {a₁ a₂ a₃ b₁ b₂ b₃ c₁ c₂ c₃ : ℝ}
    (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (ha₃ : 0 ≤ a₃) (ha : a₁ + a₂ + a₃ = 1)
    (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) (hb₃ : 0 ≤ b₃) (hb : b₁ + b₂ + b₃ = 1)
    (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hc₃ : 0 ≤ c₃) (hc : c₁ + c₂ + c₃ = 1)
    (hP : ∀ i, P i = a₁ * P' i + a₂ * Q' i + a₃ * R' i)
    (hQ : ∀ i, Q i = b₁ * P' i + b₂ * Q' i + b₃ * R' i)
    (hR : ∀ i, R i = c₁ * P' i + c₂ * Q' i + c₃ * R' i) :
    m P Q R ≤ m P' Q' R' := by
  by_cases hS0 : sideMax P' Q' R' = 0
  · -- degenerate: `P' = Q' = R'`, hence `P = Q = R` and `m P Q R = 0`
    obtain ⟨h1, h2⟩ := sideMax_eq_zero hS0
    have hPpt : P = P' := by
      apply Pt_ext
      intro i
      rw [hP i, h1, h2]
      linear_combination (R' i) * ha
    have hQpt : Q = P' := by
      apply Pt_ext
      intro i
      rw [hQ i, h1, h2]
      linear_combination (R' i) * hb
    have hRpt : R = P' := by
      apply Pt_ext
      intro i
      rw [hR i, h1, h2]
      linear_combination (R' i) * hc
    rw [hPpt, hQpt, hRpt, m_eq_zero_of_sarea_eq_zero (sarea_self_left P' P')]
    exact m_nonneg _ _ _
  · -- nondegenerate: pick the longest side of `P'Q'R'`
    rcases max_choice (dist P' Q') (max (dist Q' R') (dist R' P')) with h | h
    · -- longest side is `P'Q'`: apply the auxiliary lemma at `(R', P', Q')`
      have hmax : sideMax R' P' Q' = dist P' Q' := by
        rw [sideMax_rot Q' R' P', sideMax_rot P' Q' R']; exact h
      have hne : dist P' Q' ≠ 0 := by rw [← h]; exact hS0
      have haux := m_mono_aux (P:=P) (Q:=Q) (R:=R) (P':=R') (Q':=P') (R':=Q')
        ha₃ ha₁ ha₂ (by linarith [ha]) hb₃ hb₁ hb₂ (by linarith [hb])
        hc₃ hc₁ hc₂ (by linarith [hc])
        (fun i => by rw [hP i]; ring) (fun i => by rw [hQ i]; ring)
        (fun i => by rw [hR i]; ring) hmax hne
      rw [m_rot Q' R' P', m_rot P' Q' R'] at haux
      exact haux
    · rcases max_choice (dist Q' R') (dist R' P') with h2 | h2
      · -- longest side is `Q'R'`: apply the auxiliary lemma directly
        have hne : dist Q' R' ≠ 0 := by rw [← h.trans h2]; exact hS0
        exact m_mono_aux ha₁ ha₂ ha₃ ha hb₁ hb₂ hb₃ hb hc₁ hc₂ hc₃ hc
          hP hQ hR (h.trans h2) hne
      · -- longest side is `R'P'`: apply the auxiliary lemma at `(Q', R', P')`
        have hmax : sideMax Q' R' P' = dist R' P' := by rw [sideMax_rot]; exact h.trans h2
        have hne : dist R' P' ≠ 0 := by rw [← h.trans h2]; exact hS0
        have haux := m_mono_aux (P:=P) (Q:=Q) (R:=R) (P':=Q') (Q':=R') (R':=P')
          ha₂ ha₃ ha₁ (by linarith [ha]) hb₂ hb₃ hb₁ (by linarith [hb])
          hc₂ hc₃ hc₁ (by linarith [hc])
          (fun i => by rw [hP i]; ring) (fun i => by rw [hQ i]; ring)
          (fun i => by rw [hR i]; ring) hmax hne
        rw [m_rot P' Q' R'] at haux
        exact haux

/-! ### The case of `X` inside (or on the boundary of) the triangle -/

lemma inside_case {A B C X : Pt} (hs : sarea A B C ≠ 0)
    (h1 : 0 ≤ sarea A B C * sarea X B C)
    (h2 : 0 ≤ sarea A B C * sarea A X C)
    (h3 : 0 ≤ sarea A B C * sarea A B X) :
    m A B C ≤ m A B X + m A X C + m X B C := by
  have hs_id := sarea_id A B C X
  -- the barycentric weights of `X` are nonnegative
  have hl1 : 0 ≤ sarea X B C / sarea A B C := by
    have e : sarea X B C / sarea A B C =
        (sarea A B C * sarea X B C) / (sarea A B C * sarea A B C) := by
      field_simp
    rw [e]
    exact div_nonneg h1 (mul_self_nonneg _)
  have hl2 : 0 ≤ sarea A X C / sarea A B C := by
    have e : sarea A X C / sarea A B C =
        (sarea A B C * sarea A X C) / (sarea A B C * sarea A B C) := by
      field_simp
    rw [e]
    exact div_nonneg h2 (mul_self_nonneg _)
  have hl3 : 0 ≤ sarea A B X / sarea A B C := by
    have e : sarea A B X / sarea A B C =
        (sarea A B C * sarea A B X) / (sarea A B C * sarea A B C) := by
      field_simp
    rw [e]
    exact div_nonneg h3 (mul_self_nonneg _)
  have hlsum : sarea X B C / sarea A B C + sarea A X C / sarea A B C +
      sarea A B X / sarea A B C = 1 := by
    rw [← add_div, ← add_div, ← hs_id]
    exact div_self hs
  have hX : ∀ i, X i = (sarea X B C / sarea A B C) * A i +
      (sarea A X C / sarea A B C) * B i + (sarea A B X / sarea A B C) * C i := by
    intro i
    have h := bary_coords (A:=A) (B:=B) (C:=C) (X:=X) hs i
    field_simp
    linarith [h]
  -- the longest side of `ABC` is positive
  have hSpos : 0 < sideMax A B C := by
    have hne : sideMax A B C ≠ 0 := by
      intro hcon
      obtain ⟨hAB, -⟩ := sideMax_eq_zero hcon
      rw [hAB] at hs
      exact hs (sarea_self_left B C)
    exact lt_of_le_of_ne (sideMax_nonneg _ _ _) hne.symm
  -- distances from vertices to `X` are bounded by the longest side of `ABC`
  have hdA : dist A X ≤ sideMax A B C := by
    have k := dist_le_of_bary (P:=A) hl1 hl2 hl3 hlsum hX
    rw [dist_self, max_eq_right (le_trans dist_nonneg (le_max_left _ _))] at k
    have e : max (dist A B) (dist A C) ≤ sideMax A B C := by
      rw [max_le_iff]
      exact ⟨le_max_left _ _, le_trans (le_of_eq (dist_comm A C))
        (le_trans (le_max_right _ _) (le_max_right _ _))⟩
    exact le_trans k e
  have hdB : dist B X ≤ sideMax A B C := by
    have k := dist_le_of_bary (P:=B) hl1 hl2 hl3 hlsum hX
    rw [dist_self, max_eq_right dist_nonneg] at k
    have e : max (dist B A) (dist B C) ≤ sideMax A B C := by
      rw [max_le_iff]
      exact ⟨le_trans (le_of_eq (dist_comm B A)) (le_max_left _ _),
        le_trans (le_max_left _ _) (le_max_right _ _)⟩
    exact le_trans k e
  have hdC : dist C X ≤ sideMax A B C := by
    have k := dist_le_of_bary (P:=C) hl1 hl2 hl3 hlsum hX
    rw [dist_self, max_eq_left dist_nonneg] at k
    have e : max (dist C A) (dist C B) ≤ sideMax A B C := by
      rw [max_le_iff]
      exact ⟨le_trans (le_max_right _ _) (le_max_right _ _),
        le_trans (le_of_eq (dist_comm C B)) (le_trans (le_max_left _ _) (le_max_right _ _))⟩
    exact le_trans k e
  -- the longest sides of the three small triangles are at most that of `ABC`
  have hS1 : sideMax X B C ≤ sideMax A B C := by
    show max (dist X B) (max (dist B C) (dist C X)) ≤ sideMax A B C
    rw [max_le_iff, max_le_iff]
    exact ⟨le_trans (le_of_eq (dist_comm X B)) hdB,
      le_trans (le_max_left _ _) (le_max_right _ _), hdC⟩
  have hS2 : sideMax A X C ≤ sideMax A B C := by
    show max (dist A X) (max (dist X C) (dist C A)) ≤ sideMax A B C
    rw [max_le_iff, max_le_iff]
    exact ⟨hdA, le_trans (le_of_eq (dist_comm X C)) hdC,
      le_trans (le_max_right _ _) (le_max_right _ _)⟩
  have hS3 : sideMax A B X ≤ sideMax A B C := by
    show max (dist A B) (max (dist B X) (dist X A)) ≤ sideMax A B C
    rw [max_le_iff, max_le_iff]
    exact ⟨le_max_left _ _, hdB, le_trans (le_of_eq (dist_comm X A)) hdA⟩
  -- the absolute areas split
  have habs : |sarea A B C| = |sarea X B C| + |sarea A X C| + |sarea A B X| := by
    rcases lt_or_gt_of_ne hs with h | h
    · have hs1 : sarea X B C ≤ 0 := by
        by_contra hcon
        push Not at hcon
        have hbad : sarea A B C * sarea X B C < 0 := mul_neg_of_neg_of_pos h hcon
        linarith [h1, hbad]
      have hs2 : sarea A X C ≤ 0 := by
        by_contra hcon
        push Not at hcon
        have hbad : sarea A B C * sarea A X C < 0 := mul_neg_of_neg_of_pos h hcon
        linarith [h2, hbad]
      have hs3 : sarea A B X ≤ 0 := by
        by_contra hcon
        push Not at hcon
        have hbad : sarea A B C * sarea A B X < 0 := mul_neg_of_neg_of_pos h hcon
        linarith [h3, hbad]
      rw [abs_of_nonpos h.le, abs_of_nonpos hs1, abs_of_nonpos hs2, abs_of_nonpos hs3]
      linarith [hs_id]
    · have hs1 : 0 ≤ sarea X B C := nonneg_of_mul_nonneg_right h1 h
      have hs2 : 0 ≤ sarea A X C := nonneg_of_mul_nonneg_right h2 h
      have hs3 : 0 ≤ sarea A B X := nonneg_of_mul_nonneg_right h3 h
      rw [abs_of_nonneg h.le, abs_of_nonneg hs1, abs_of_nonneg hs2, abs_of_nonneg hs3]
      linarith [hs_id]
  -- rewrite the LHS as a sum of three fractions
  have hm : m A B C = 2 * |sarea X B C| / sideMax A B C +
      2 * |sarea A X C| / sideMax A B C + 2 * |sarea A B X| / sideMax A B C := by
    unfold m
    rw [habs]
    ring
  -- each fraction is at most the corresponding `m`
  have ht1 : 2 * |sarea X B C| / sideMax A B C ≤ m X B C := by
    by_cases hs1z : sarea X B C = 0
    · rw [hs1z, abs_zero, mul_zero, zero_div]
      exact m_nonneg _ _ _
    · have hS1pos : 0 < sideMax X B C := by
        have hne : sideMax X B C ≠ 0 := by
          intro hcon
          obtain ⟨g1, g2⟩ := sideMax_eq_zero hcon
          apply hs1z
          rw [g1, g2]
          exact sarea_self_left C C
        exact lt_of_le_of_ne (sideMax_nonneg _ _ _) hne.symm
      unfold m
      exact div_le_div_of_nonneg_left (mul_nonneg (by norm_num) (abs_nonneg _)) hS1pos hS1
  have ht2 : 2 * |sarea A X C| / sideMax A B C ≤ m A X C := by
    by_cases hs2z : sarea A X C = 0
    · rw [hs2z, abs_zero, mul_zero, zero_div]
      exact m_nonneg _ _ _
    · have hS2pos : 0 < sideMax A X C := by
        have hne : sideMax A X C ≠ 0 := by
          intro hcon
          obtain ⟨g1, -⟩ := sideMax_eq_zero hcon
          apply hs2z
          rw [g1]
          exact sarea_self_left X C
        exact lt_of_le_of_ne (sideMax_nonneg _ _ _) hne.symm
      unfold m
      exact div_le_div_of_nonneg_left (mul_nonneg (by norm_num) (abs_nonneg _)) hS2pos hS2
  have ht3 : 2 * |sarea A B X| / sideMax A B C ≤ m A B X := by
    by_cases hs3z : sarea A B X = 0
    · rw [hs3z, abs_zero, mul_zero, zero_div]
      exact m_nonneg _ _ _
    · have hS3pos : 0 < sideMax A B X := by
        have hne : sideMax A B X ≠ 0 := by
          intro hcon
          obtain ⟨g1, -⟩ := sideMax_eq_zero hcon
          apply hs3z
          rw [g1]
          exact sarea_self_left B X
        exact lt_of_le_of_ne (sideMax_nonneg _ _ _) hne.symm
      unfold m
      exact div_le_div_of_nonneg_left (mul_nonneg (by norm_num) (abs_nonneg _)) hS3pos hS3
  -- assemble
  rw [hm]
  linarith [ht1, ht2, ht3]

/-! ### The case of `X` outside the triangle -/

lemma outside_case {A B C X : Pt} (hs : sarea A B C ≠ 0)
    (h1 : sarea A B C * sarea X B C < 0) :
    m A B C ≤ m A B X + m A X C + m X B C := by
  have hs_id := sarea_id A B C X
  have hss1 : sarea A B C - sarea X B C ≠ 0 := by
    rcases mul_neg_iff.mp h1 with ⟨g1, g2⟩ | ⟨g1, g2⟩
    · have : 0 < sarea A B C - sarea X B C := by linarith
      exact ne_of_gt this
    · have : sarea A B C - sarea X B C < 0 := by linarith
      exact ne_of_lt this
  -- `O`, the intersection of segment `AX` with line `BC`, via the parameter `t`
  set t := sarea A B C / (sarea A B C - sarea X B C) with ht_def
  have ht : t * (sarea A B C - sarea X B C) = sarea A B C := div_mul_cancel₀ _ hss1
  have ht0 : 0 < t := by
    rcases mul_neg_iff.mp h1 with ⟨g1, g2⟩ | ⟨g1, g2⟩
    · exact div_pos g1 (by linarith)
    · exact div_pos_of_neg_of_neg g1 (by linarith)
  have ht1 : t < 1 := by
    rcases mul_neg_iff.mp h1 with ⟨g1, g2⟩ | ⟨g1, g2⟩
    · rw [ht_def, div_lt_one (by linarith : 0 < sarea A B C - sarea X B C)]
      linarith
    · rw [ht_def, div_lt_iff_of_neg (by linarith : sarea A B C - sarea X B C < 0)]
      linarith
  set O : Pt := (1 - t) • A + t • X with hO_def
  have hOi : ∀ i, O i = (1 - t) * A i + t * X i := by
    intro i
    simp [hO_def, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  have hsO1 : sarea O B C = 0 := by
    have e : sarea O B C = (1 - t) * sarea A B C + t * sarea X B C := by
      simp only [sarea, cross, hOi, PiLp.sub_apply]
      ring
    rw [e]
    have e2 : (1 - t) * sarea A B C + t * sarea X B C =
        sarea A B C - t * (sarea A B C - sarea X B C) := by ring
    rw [e2, ht, sub_self]
  have hsO2 : sarea A O C = t * sarea A X C := by
    simp only [sarea, cross, hOi, PiLp.sub_apply]
    ring
  have hsO3 : sarea A B O = t * sarea A B X := by
    simp only [sarea, cross, hOi, PiLp.sub_apply]
    ring
  -- the position of `O` on line `BC`, measured from `B` towards `C`
  have hkey : ∀ i, sarea A B C * (O i - B i) = t * sarea A B X * (C i - B i) := by
    intro i
    have hbary := bary_coords (A:=A) (B:=B) (C:=C) (X:=X) hs i
    rw [hOi]
    linear_combination (B i - A i) * ht + t * hbary - (t * B i) * hs_id
  -- at least one of the other two signed areas has the sign of `sarea A B C`
  have hpos : 0 < sarea A B C * (sarea A B C - sarea X B C) := by
    rcases mul_neg_iff.mp h1 with ⟨g1, g2⟩ | ⟨g1, g2⟩
    · exact mul_pos g1 (by linarith)
    · exact mul_pos_of_neg_of_neg g1 (by linarith)
  have hsum23 : 0 < sarea A B C * sarea A X C + sarea A B C * sarea A B X := by
    have e : sarea A B C * sarea A X C + sarea A B C * sarea A B X =
        sarea A B C * (sarea A X C + sarea A B X) := by ring
    rw [e]
    have e2 : sarea A X C + sarea A B X = sarea A B C - sarea X B C := by linarith [hs_id]
    rw [e2]
    exact hpos
  by_cases h3' : 0 ≤ sarea A B C * sarea A B X
  · by_cases h2' : 0 ≤ sarea A B C * sarea A X C
    · -- `O` lies on segment `BC`: the inside case applies at `O`
      have e2 : sarea A B C * (t * sarea A X C) = t * (sarea A B C * sarea A X C) := by ring
      have e3 : sarea A B C * (t * sarea A B X) = t * (sarea A B C * sarea A B X) := by ring
      have hin := inside_case (A:=A) (B:=B) (C:=C) (X:=O) hs
        (by simp [hsO1]) (by rw [hsO2, e2]; exact mul_nonneg ht0.le h2')
        (by rw [hsO3, e3]; exact mul_nonneg ht0.le h3')
      have hmO : m O B C = 0 := m_eq_zero_of_sarea_eq_zero hsO1
      have hle1 : m A B O ≤ m A B X := by
        exact m_mono (P:=A) (Q:=B) (R:=O) (P':=A) (Q':=B) (R':=X)
          one_pos.le (le_refl 0) (le_refl 0) (by norm_num)
          (le_refl 0) one_pos.le (le_refl 0) (by norm_num)
          (sub_nonneg.mpr ht1.le) (le_refl 0) ht0.le (by ring)
          (fun i => by ring) (fun i => by ring) (fun i => by rw [hOi i]; ring)
      have hle2 : m A O C ≤ m A X C := by
        exact m_mono (P:=A) (Q:=O) (R:=C) (P':=A) (Q':=X) (R':=C)
          one_pos.le (le_refl 0) (le_refl 0) (by norm_num)
          (sub_nonneg.mpr ht1.le) ht0.le (le_refl 0) (by ring)
          (le_refl 0) (le_refl 0) one_pos.le (by norm_num)
          (fun i => by ring) (fun i => by rw [hOi i]; ring) (fun i => by ring)
      have g3 := m_nonneg X B C
      linarith [hin, hmO, hle1, hle2, g3]
    · -- `sarea A B C * sarea A X C < 0`: `C` lies inside `ABX`, so `m A B C ≤ m A B X`
      push Not at h2'
      have h3pos : 0 < sarea A B C * sarea A B X := by linarith [hsum23, h2']
      set u := t * sarea A B X / sarea A B C with hu_def
      have e : t * sarea A B X - sarea A B C = -t * sarea A X C := by
        have h23 : sarea A B C - sarea X B C = sarea A X C + sarea A B X := by
          linarith [hs_id]
        linear_combination ht - t * h23
      have hu1 : 1 < u := by
        by_cases hspos : 0 < sarea A B C
        · have h2neg : sarea A X C < 0 := by
            by_contra hcon
            push Not at hcon
            have := mul_nonneg hspos.le hcon
            linarith [h2', this]
          have hnt : 0 < -t * sarea A X C := mul_pos_of_neg_of_neg (neg_neg_of_pos ht0) h2neg
          have hts : sarea A B C < t * sarea A B X := by linarith [e, hnt]
          rw [hu_def, lt_div_iff₀ hspos]
          linarith [hts]
        · have hsneg : sarea A B C < 0 := lt_of_le_of_ne (le_of_not_gt hspos) hs
          have h2pos : 0 < sarea A X C := by
            by_contra hcon
            push Not at hcon
            have := mul_nonneg_of_nonpos_of_nonpos hsneg.le hcon
            linarith [h2', this]
          have hnt : -t * sarea A X C < 0 := mul_neg_of_neg_of_pos (neg_neg_of_pos ht0) h2pos
          have hts : t * sarea A B X < sarea A B C := by linarith [e, hnt]
          rw [hu_def, lt_div_iff_of_neg hsneg]
          linarith [hts]
      set w := 1 / u with hw_def
      have hw0 : 0 < w := by rw [hw_def]; exact div_pos zero_lt_one (lt_trans zero_lt_one hu1)
      have hw1 : w < 1 := by
        rw [hw_def, div_lt_one (lt_trans zero_lt_one hu1)]
        exact hu1
      have hwu : w * u = 1 := by
        rw [hw_def]
        exact div_mul_cancel₀ 1 (ne_of_gt (lt_trans zero_lt_one hu1))
      have keyC : ∀ i, C i = (1 - w) * B i + w * O i := by
        intro i
        have hui : O i = B i + u * (C i - B i) := by
          have hk := hkey i
          rw [hu_def]
          field_simp
          linarith [hk]
        rw [hui]
        linear_combination (-(C i - B i)) * hwu
      have hle : m A B C ≤ m A B X := by
        exact m_mono (P:=A) (Q:=B) (R:=C) (P':=A) (Q':=B) (R':=X)
          one_pos.le (le_refl 0) (le_refl 0) (by norm_num)
          (le_refl 0) one_pos.le (le_refl 0) (by norm_num)
          (mul_nonneg hw0.le (sub_nonneg.mpr ht1.le)) (sub_nonneg.mpr hw1.le)
          (mul_nonneg hw0.le ht0.le) (by ring)
          (fun i => by ring) (fun i => by ring)
          (fun i => by
            have h2i := hOi i
            have h3i := keyC i
            rw [h3i, h2i]
            ring)
      have g2 := m_nonneg A X C
      have g3 := m_nonneg X B C
      linarith [hle, g2, g3]
  · -- `sarea A B C * sarea A B X < 0`: `B` lies inside `AXC`, so `m A B C ≤ m A X C`
    push Not at h3'
    have h2pos : 0 < sarea A B C * sarea A X C := by linarith [hsum23, h3']
    set u := t * sarea A B X / sarea A B C with hu_def
    have hu0 : u < 0 := by
      have e : sarea A B X / sarea A B C < 0 := by
        rw [div_neg_iff]
        rcases mul_neg_iff.mp h1 with ⟨g1, g2⟩ | ⟨g1, g2⟩
        · have hs3 : sarea A B X < 0 := by
            by_contra hcon
            push Not at hcon
            have := mul_nonneg g1.le hcon
            linarith [h3', this]
          exact Or.inr ⟨hs3, g1⟩
        · have hs3 : 0 < sarea A B X := by
            by_contra hcon
            push Not at hcon
            have := mul_nonneg_of_nonpos_of_nonpos g1.le hcon
            linarith [h3', this]
          exact Or.inl ⟨hs3, g1⟩
      rw [hu_def, mul_div_assoc]
      exact mul_neg_of_pos_of_neg ht0 e
    have h1u : 0 < 1 - u := by linarith [hu0]
    set v := -u / (1 - u) with hv_def
    have hv0 : 0 < v := by rw [hv_def]; exact div_pos (by linarith [hu0]) h1u
    have hv1 : v < 1 := by
      rw [hv_def, div_lt_one h1u]
      linarith [hu0]
    have keyB : ∀ i, B i = (1 - v) * O i + v * C i := by
      intro i
      have hui : O i = B i + u * (C i - B i) := by
        have hk := hkey i
        rw [hu_def]
        field_simp
        linarith [hk]
      rw [hui, hv_def]
      field_simp [h1u.ne']
      ring
    have hle : m A B C ≤ m A X C := by
      exact m_mono (P:=A) (Q:=B) (R:=C) (P':=A) (Q':=X) (R':=C)
        one_pos.le (le_refl 0) (le_refl 0) (by norm_num)
        (mul_nonneg (sub_nonneg.mpr hv1.le) (sub_nonneg.mpr ht1.le))
        (mul_nonneg (sub_nonneg.mpr hv1.le) ht0.le) hv0.le (by ring)
        (le_refl 0) (le_refl 0) one_pos.le (by norm_num)
        (fun i => by ring)
        (fun i => by
          have h2i := hOi i
          have h3i := keyB i
          rw [h3i, h2i]
          ring)
        (fun i => by ring)
    have g1 := m_nonneg A B X
    have g3 := m_nonneg X B C
    linarith [hle, g1, g3]

snip end

problem imo1993_p4 : ∀ A B C X : Pt, m A B C ≤ m A B X + m A X C + m X B C := by
  intro A B C X
  by_cases hs : sarea A B C = 0
  · rw [m_eq_zero_of_sarea_eq_zero hs]
    have g1 := m_nonneg A B X
    have g2 := m_nonneg A X C
    have g3 := m_nonneg X B C
    linarith
  · by_cases h1 : 0 ≤ sarea A B C * sarea X B C
    · by_cases h2 : 0 ≤ sarea A B C * sarea A X C
      · by_cases h3 : 0 ≤ sarea A B C * sarea A B X
        · exact inside_case hs h1 h2 h3
        · -- `sarea A B C * sarea A B X < 0`: reduce to `outside_case` at `(C, B, A, X)`
          push Not at h3
          have e1 : sarea C B A = -sarea A B C := by
            have hCAB : sarea C A B = sarea A B C := by
              rw [sarea_rot B C A, sarea_rot A B C]
            have hswap := sarea_swap32 C B A
            linarith
          have e2 : sarea X B A = -sarea A B X := by
            have hXAB : sarea X A B = sarea A B X := by
              rw [sarea_rot B X A, sarea_rot A B X]
            have hswap := sarea_swap32 X B A
            linarith
          have hs' : sarea C B A ≠ 0 := by
            rw [e1]; exact neg_ne_zero.mpr hs
          have h1' : sarea C B A * sarea X B A < 0 := by
            rw [e1, e2, neg_mul_neg]; exact h3
          have h := outside_case hs' h1'
          have t1 : m C B A = m A B C := by
            have k1 := (m_swap32 C B A).symm
            have k2 := m_rot B C A
            have k3 := m_rot A B C
            linarith
          have t2 : m C B X = m X B C := by
            have k1 := (m_swap21 C B X).symm
            have k2 := m_rot X B C
            linarith
          have t3 : m C X A = m A X C := by
            have k1 := (m_swap32 C X A).symm
            have k2 := (m_rot C A X).symm
            linarith
          have t4 : m X B A = m A B X := by
            have k1 := (m_swap21 X B A).symm
            have k2 := m_rot A B X
            linarith
          linarith [h, t1, t2, t3, t4]
      · -- `sarea A B C * sarea A X C < 0`: reduce to `outside_case` at `(B, A, C, X)`
        push Not at h2
        have hs' : sarea B A C ≠ 0 := by
          have e := sarea_swap21 A B C
          intro hcon
          apply hs
          linarith [e, hcon]
        have h1' : sarea B A C * sarea X A C < 0 := by
          have e1 := sarea_swap21 A B C
          have e2 := sarea_swap21 A X C
          rw [e1, e2, neg_mul_neg]; exact h2
        have h := outside_case hs' h1'
        have t1 : m B A C = m A B C := (m_swap21 B A C).symm
        have t2 : m B A X = m A B X := (m_swap21 B A X).symm
        have t3 : m B X C = m X B C := (m_swap21 B X C).symm
        have t4 : m X A C = m A X C := (m_swap21 X A C).symm
        linarith [h, t1, t2, t3, t4]
    · push Not at h1
      exact outside_case hs h1

end Imo1993P4
